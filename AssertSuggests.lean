import Lean.Elab.Command
import Lean.Elab.Quotation
import Lean.Server.InfoUtils
import Lean.Server.CodeActions
import Lean.Meta.TryThis


namespace AssertSuggests

open Lean Elab Command Server Meta Tactic.TryThis Term.Quotation

private partial def foldInfoTreeIncludingContextFree (f : Info → α → α) (init : α) : InfoTree → α
  | .context _ t => foldInfoTreeIncludingContextFree f init t
  | .node i ts =>
    let a := f i init
    ts.foldl (init := a) (foldInfoTreeIncludingContextFree f)
  | .hole _ => init

private def tryThisEditFromInfo? : Info → Option Lsp.TextEdit
  | .ofCustomInfo { value, .. } => (value.get? TryThisInfo).map (·.edit)
  | _ => none

private def collectTryThisEdits (trees : Array InfoTree) : Array Lsp.TextEdit :=
  trees.foldl (init := #[]) fun edits tree =>
    foldInfoTreeIncludingContextFree (init := edits) (fun info acc =>
      (tryThisEditFromInfo? info).elim acc acc.push) tree

private def extractSourceText (text : FileMap) (range : Lsp.Range) : String :=
  let startPos := text.lspPosToUtf8Pos range.start
  let endPos := text.lspPosToUtf8Pos range.«end»
  String.Pos.Raw.extract text.source startPos endPos

structure SuggestionEdit where
  before : String
  after : String

private def lspEditToSuggestionEdit (text : FileMap) (edit : Lsp.TextEdit) : SuggestionEdit :=
  { before := extractSourceText text edit.range, after := edit.newText }

structure SuggestionMismatch where
  catName : Name
  linterName? : Option Name
  actualEdits : Array SuggestionEdit
  deriving TypeName

private def pushMismatchToInfoTree (stx : Syntax) (catName : Name) (linterName? : Option Name)
    (actualEdits : Array SuggestionEdit) : CommandElabM Unit :=
  pushInfoLeaf (.ofCustomInfo { stx, value := Dynamic.mk (SuggestionMismatch.mk catName linterName? actualEdits) })

private def renderAssertSuggestsPrefix (catName : Name) (linterName? : Option Name)
    (actualEdits : Array SuggestionEdit) : String :=
  let linterPrefix := linterName?.elim "" (s!"{·} ")
  if actualEdits.isEmpty then
    s!"#assertSuggests {linterPrefix}"
  else
    let formattedPairs := actualEdits.map fun { before, after } =>
      s!"`({catName}| {before.trim}) => `({catName}| {after.trim})"
    s!"#assertSuggests {linterPrefix}{", ".intercalate formattedPairs.toList} "

syntax suggestionPair := term " => " term
syntax (name := assertSuggestsCmd)
  "#assertSuggests " (ident)? sepBy1(suggestionPair, ", ") " in " command : command
syntax (name := assertNoSuggestsCmd)
  "#assertNoSuggests " (ident)? "in " command : command

private def verifyReprintedQuotation (quotStx : Syntax) (actual : String) (label : String) (idx : Nat)
    : CommandElabM Bool := do
  match quotStx.getQuotContent.reprint with
  | some expectedText =>
    if expectedText.trim == actual.trim then return true
    logWarningAt quotStx
      m!"{label} mismatch for suggestion {idx}:\n  expected: {expectedText.trim}\n  actual:   {actual.trim}"
    return false
  | none =>
    logWarningAt quotStx m!"could not reprint expected {label} syntax for suggestion {idx}"
    return false

private def verifySuggestionPair (text : FileMap) (edit : Lsp.TextEdit)
    (pairStx : TSyntax `AssertSuggests.suggestionPair) (idx : Nat)
    : CommandElabM (SuggestionEdit × Bool) := do
  let `(suggestionPair| $before => $after) := pairStx | throwError "unexpected suggestionPair syntax"
  let suggestion := lspEditToSuggestionEdit text edit
  let beforeOk ← verifyReprintedQuotation before.raw suggestion.before "before" idx
  let afterOk ← verifyReprintedQuotation after.raw suggestion.after "after" idx
  return (suggestion, beforeOk && afterOk)

private def elabCommandSilently (cmd : Syntax) : CommandElabM Unit :=
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    withReader ({ · with snap? := none }) do
      elabCommand cmd

private def runLinterAndCollectTrees (linter : Linter) (cmd : Syntax)
    : CommandElabM (PersistentArray InfoTree) := do
  setInfoState { enabled := true, trees := {} }
  try
    linter.run cmd
  catch
    | .error ref msg =>
      logException (.error ref m!"linter {.ofConstName linter.name} failed: {msg}")
    | ex@(.internal _ _) =>
      logException ex
  let trees := (← getInfoState).trees
  enableInfoTree false
  return trees

private def withInfoCollectionDisabled (action : CommandElabM α) : CommandElabM α :=
  withEnableInfoTree false action

private def scheduleLinterRestore : CommandElabM Unit := do
  let previousLinters ← lintersRef.get
  lintersRef.set #[{
    run := fun _ => do lintersRef.set previousLinters
    name := `AssertSuggests.restoreLinters
  }]

private def elabCommandAndCollectSuggestionEdits (cmd : Syntax) (linterName? : Option Name := none)
    : CommandElabM (Array Lsp.TextEdit) := do
  let enableLinterScope := linterName?.elim id fun name (scope : Scope) =>
    { scope with opts := scope.opts.insert (`linter ++ name) (.ofBool true) }
  withScope enableLinterScope do
    let collectedTrees ← withInfoCollectionDisabled do
      elabCommandSilently cmd
      let linters ← lintersRef.get
      withoutModifyingEnv do
        let mut collectedTrees : Array InfoTree := #[]
        for linter in linters do
          let trees ← runLinterAndCollectTrees linter cmd
          collectedTrees := trees.foldl (init := collectedTrees) fun a t => a.push t
        return collectedTrees
    modify fun s => { s with messages := .empty }
    scheduleLinterRestore
    return collectTryThisEdits collectedTrees

@[command_elab assertSuggestsCmd] def elabAssertSuggests : CommandElab
  | stx@`(command| #assertSuggests $[$linterName?:ident]? $pairs,* in $cmd) => do
    let linterName? := linterName?.map (·.getId)
    let edits ← elabCommandAndCollectSuggestionEdits cmd linterName?
    let text ← getFileMap
    let pairStxs := pairs.getElems
    let catName ← if h : 0 < pairStxs.size then
        match pairStxs[0] with
        | `(suggestionPair| $before => $_) => liftTermElabM (getQuotKind before)
        | _ => pure `tactic
      else pure `tactic
    if edits.size != pairStxs.size then
      logWarningAt stx m!"expected {pairStxs.size} suggestion(s) but got {edits.size}"
      pushMismatchToInfoTree stx catName linterName? (edits.map (lspEditToSuggestionEdit text))
      return
    let results ← (edits.zip pairStxs).mapIdxM fun idx (edit, pairStx) =>
      verifySuggestionPair text edit pairStx (idx + 1)
    unless results.all (·.2) do
      pushMismatchToInfoTree stx catName linterName? (results.map (·.1))
  | _ => throwUnsupportedSyntax

@[command_elab assertNoSuggestsCmd] def elabAssertNoSuggests : CommandElab
  | stx@`(command| #assertNoSuggests $[$linterName?:ident]? in $cmd) => do
    let edits ← elabCommandAndCollectSuggestionEdits cmd (linterName?.map (·.getId))
    unless edits.isEmpty do
      let text ← getFileMap
      let descriptions := edits.map fun edit =>
        let { before, after } := lspEditToSuggestionEdit text edit
        s!"  `{before.trim}` => `{after.trim}`"
      logWarningAt stx
        m!"expected no suggestions but got {edits.size}:\n{"\n".intercalate descriptions.toList}"
  | _ => throwUnsupportedSyntax

open CodeAction Server RequestM in
@[command_code_action assertSuggestsCmd]
def updateAssertSuggestsCodeAction : CommandCodeAction := fun _ _ _ node => do
  let .node _ ts := node | return #[]
  let mismatch? := ts.findSome? fun
    | .node (.ofCustomInfo { stx, value }) _ => do
      let m ← value.get? SuggestionMismatch; return (stx, m)
    | _ => none
  let some (stx, mismatch) := mismatch? | return #[]
  let doc ← readDoc
  let baseCodeAction := {
    title := "Update #assertSuggests with actual suggestions"
    kind? := "quickfix"
    isPreferred? := true
  }
  pure #[{
    eager := baseCodeAction
    lazy? := some do
      let some start := stx.getPos? true | return baseCodeAction
      let some inKeywordPos := stx[3].getPos? true | return baseCodeAction
      let newText := renderAssertSuggestsPrefix mismatch.catName mismatch.linterName? mismatch.actualEdits
      pure { baseCodeAction with
        edit? := some <| .ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, inKeywordPos⟩
          newText
        }
      }
  }]

end AssertSuggests
