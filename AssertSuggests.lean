import Lean.Elab.Command
import Lean.Elab.Quotation
import Lean.Server.InfoUtils
import Lean.Server.CodeActions
import Lean.Meta.TryThis


namespace AssertSuggests

open Lean Elab Command Server Meta Tactic.TryThis Term.Quotation

/-- Fold over all `Info` nodes in an `InfoTree`, including context-free ones.
Unlike `InfoTree.foldInfo`, this does not require a `ContextInfo` wrapper. -/
private partial def foldInfoAll (f : Info → α → α) (init : α) : InfoTree → α
  | .context _ t => foldInfoAll f init t
  | .node i ts =>
    let a := f i init
    ts.foldl (init := a) (foldInfoAll f)
  | .hole _ => init

/-- Try to extract a `TryThisInfo` edit from a single `Info` node. -/
private def tryThisEdit? : Info → Option Lsp.TextEdit
  | .ofCustomInfo { value, .. } => (value.get? TryThisInfo).map (·.edit)
  | _ => none

/-- Extract `TryThisInfo` edits from an array of info trees. -/
private def extractEdits (trees : PersistentArray InfoTree) : Array Lsp.TextEdit :=
  trees.foldl (init := #[]) fun edits tree =>
    edits ++ foldInfoAll (init := #[]) (fun info acc =>
      match tryThisEdit? info with
      | some edit => acc.push edit
      | none => acc) tree

/-- Extract old text from a file map given an LSP range. -/
private def getOldText (text : FileMap) (range : Lsp.Range) : String :=
  let startPos := text.lspPosToUtf8Pos range.start
  let endPos := text.lspPosToUtf8Pos range.«end»
  String.Pos.Raw.extract text.source startPos endPos

/-- The before/after text of a single suggestion edit. -/
structure SuggestionEdit where
  before : String
  after : String

/-- Extract a `SuggestionEdit` from a single LSP edit. -/
private def editToSuggestion (text : FileMap) (edit : Lsp.TextEdit) : SuggestionEdit :=
  { before := getOldText text edit.range, after := edit.newText }

/-- Data stored in the info tree when `#assertSuggests` detects a mismatch,
used by the code action to suggest the correct text. -/
structure Failure where
  catName : Name
  linterName? : Option Name
  actual : Array SuggestionEdit
  deriving TypeName

/-- Push a `Failure` into the info tree for the code action to pick up. -/
private def pushFailure (stx : Syntax) (catName : Name) (linterName? : Option Name)
    (actual : Array SuggestionEdit) : CommandElabM Unit :=
  pushInfoLeaf (.ofCustomInfo { stx, value := Dynamic.mk (Failure.mk catName linterName? actual) })

/-- Format the replacement text for the prefix of an `#assertSuggests` command
(everything before the `in` keyword). -/
private def formatAssertSuggestsPrefix (catName : Name) (linterName? : Option Name)
    (actual : Array SuggestionEdit) : String :=
  let linterPart := match linterName? with
    | some n => s!"{n} "
    | none => ""
  if actual.isEmpty then
    s!"#assertSuggests {linterPart}"
  else
    let pairsText := actual.toList.map fun { before, after } =>
      s!"`({catName}| {before.trim}) => `({catName}| {after.trim})"
    s!"#assertSuggests {linterPart}{", ".intercalate pairsText} "

syntax suggestionPair := term " => " term
syntax (name := assertSuggestsCmd)
  "#assertSuggests " (ident)? sepBy1(suggestionPair, ", ") " in " command : command
syntax (name := assertNoSuggestsCmd)
  "#assertNoSuggests " (ident)? "in " command : command

/-- Check that reprinted quotation content matches actual text. Returns `true` on match. -/
private def checkReprint (quotStx : Syntax) (actual : String) (label : String) (idx : Nat)
    : CommandElabM Bool := do
  match quotStx.getQuotContent.reprint with
  | some expectedText =>
    if expectedText.trim == actual.trim then return true
    logErrorAt quotStx
      m!"{label} mismatch for suggestion {idx}:\n  expected: {expectedText.trim}\n  actual:   {actual.trim}"
    return false
  | none =>
    logErrorAt quotStx m!"could not reprint expected {label} syntax for suggestion {idx}"
    return false

/-- Compare one edit against its expected before/after quotation pair.
Returns the actual suggestion and whether the pair matched. -/
private def comparePair (text : FileMap) (edit : Lsp.TextEdit)
    (pairStx : TSyntax `AssertSuggests.suggestionPair) (idx : Nat)
    : CommandElabM (SuggestionEdit × Bool) := do
  let `(suggestionPair| $before => $after) := pairStx | throwError "unexpected suggestionPair syntax"
  let suggestion := editToSuggestion text edit
  let beforeOk ← checkReprint before.raw suggestion.before "before" idx
  let afterOk ← checkReprint after.raw suggestion.after "after" idx
  return (suggestion, beforeOk && afterOk)

/-- Run the inner command and linters, collecting TryThisInfo edits.
If `linterName?` is provided, the corresponding `linter.NAME` option is enabled. -/
private def runAndCollectEdits (cmd : Syntax) (linterName? : Option Name := none)
    : CommandElabM (Array Lsp.TextEdit) := do
  let setLinterOpt := match linterName? with
    | some name => fun (scope : Scope) =>
      { scope with opts := scope.opts.insert (`linter ++ name) (.ofBool true) }
    | none => id
  withScope setLinterOpt do
    let savedEnabled := (← getInfoState).enabled
    modifyInfoState fun s => { s with enabled := false }
    let infoRef ← IO.mkRef (PersistentArray.empty : PersistentArray InfoTree)
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
      withReader ({ · with snap? := none }) do
        elabCommand cmd
    let linters ← lintersRef.get
    withoutModifyingEnv do
      for linter in linters do
        modifyInfoState fun _ => { enabled := true, trees := {} }
        try
          linter.run cmd
        catch ex =>
          match ex with
          | .error ref msg =>
            logException (.error ref m!"linter {.ofConstName linter.name} failed: {msg}")
          | .internal _ _ =>
            logException ex
        let linterTrees := (← getInfoState).trees
        infoRef.modify (· ++ linterTrees)
        modifyInfoState fun _ => { enabled := false }
    modifyInfoState fun s => { s with enabled := savedEnabled }
    modify fun s => { s with messages := .empty }
    let savedLinters ← lintersRef.get
    lintersRef.set #[{
      run := fun _ => do lintersRef.set savedLinters
      name := `AssertSuggests.restoreLinters
    }]
    return extractEdits (← infoRef.get)

@[command_elab assertSuggestsCmd] def elabAssertSuggests : CommandElab
  | stx@`(command| #assertSuggests $[$linterName?:ident]? $pairs,* in $cmd) => do
    let linterName? := linterName?.map (·.getId)
    let edits ← runAndCollectEdits cmd linterName?
    let text ← getFileMap
    let pairStxs := pairs.getElems
    let catName ← if h : 0 < pairStxs.size then
        match pairStxs[0] with
        | `(suggestionPair| $before => $_) => liftTermElabM (getQuotKind before)
        | _ => pure `tactic
      else pure `tactic
    if edits.size != pairStxs.size then
      logErrorAt stx m!"expected {pairStxs.size} suggestion(s) but got {edits.size}"
      pushFailure stx catName linterName? (edits.map (editToSuggestion text))
      return
    let results ← (edits.zip pairStxs).mapIdxM fun idx (edit, pairStx) =>
      comparePair text edit pairStx (idx + 1)
    unless results.all (·.2) do
      pushFailure stx catName linterName? (results.map (·.1))
  | _ => throwUnsupportedSyntax

@[command_elab assertNoSuggestsCmd] def elabAssertNoSuggests : CommandElab
  | stx@`(command| #assertNoSuggests $[$linterName?:ident]? in $cmd) => do
    let edits ← runAndCollectEdits cmd (linterName?.map (·.getId))
    if !edits.isEmpty then
      let text ← getFileMap
      let descriptions := edits.map fun edit =>
        let { before, after } := editToSuggestion text edit
        s!"  `{before.trim}` => `{after.trim}`"
      logErrorAt stx
        m!"expected no suggestions but got {edits.size}:\n{"\n".intercalate descriptions.toList}"
  | _ => throwUnsupportedSyntax

open CodeAction Server RequestM in
@[command_code_action assertSuggestsCmd]
def assertSuggestsCodeAction : CommandCodeAction := fun _ _ _ node => do
  let .node _ ts := node | return #[]
  let res := ts.findSome? fun
    | .node (.ofCustomInfo { stx, value }) _ => do
      let f ← value.get? Failure; return (stx, f)
    | _ => none
  let some (stx, failure) := res | return #[]
  let doc ← readDoc
  let eager := {
    title := "Update #assertSuggests with actual suggestions"
    kind? := "quickfix"
    isPreferred? := true
  }
  pure #[{
    eager
    lazy? := some do
      let some start := stx.getPos? true | return eager
      -- End the range at the `in` keyword (arg 3), preserving `in` and any following whitespace.
      let some inStart := stx[3].getPos? true | return eager
      let newText := formatAssertSuggestsPrefix failure.catName failure.linterName? failure.actual
      pure { eager with
        edit? := some <| .ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, inStart⟩
          newText
        }
      }
  }]

end AssertSuggests
