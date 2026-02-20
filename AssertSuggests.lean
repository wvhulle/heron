/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Lean.Elab.Command
import Lean.Elab.Quotation
import Lean.Server.InfoUtils
import Lean.Server.CodeActions
import Lean.Meta.TryThis

/-!
# `#assertSuggests` / `#assertNoSuggests` Commands

`#assertSuggests` elaborates an inner command, extracts `TryThisInfo` suggestions from
the info tree, and compares the edit diffs against expected before/after pairs
provided as syntax quotations.

The optional linter name argument enables that linter for the inner command,
removing the need for `set_option linter.xxx true in`.

```lean
-- Verify that a linter transforms `before` into `after`:
#assertSuggests simpRfl `(tactic| simp; rfl) => `(tactic| simp) in
example (a : Nat) : a + 0 = a := by
  simp; rfl

-- Assert no suggestions produced:
#assertNoSuggests in
example (a : Nat) : a + 0 = a := by
  simp
```
-/

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

/-- Extract `TryThisInfo` edits from an array of info trees. -/
private def extractEdits (trees : PersistentArray InfoTree) : Array Lsp.TextEdit := Id.run do
  let mut edits : Array Lsp.TextEdit := #[]
  for tree in trees do
    let infos := foldInfoAll (init := #[]) (fun info acc =>
      match info with
      | .ofCustomInfo { value, .. } =>
        match value.get? TryThisInfo with
        | some tryThisInfo => acc.push tryThisInfo.edit
        | none => acc
      | _ => acc) tree
    edits := edits ++ infos
  return edits

/-- Extract old text from a file map given an LSP range. -/
private def getOldText (text : FileMap) (range : Lsp.Range) : String :=
  let startPos := text.lspPosToUtf8Pos range.start
  let endPos := text.lspPosToUtf8Pos range.«end»
  String.Pos.Raw.extract text.source startPos endPos

/-- Data stored in the info tree when `#assertSuggests` detects a mismatch,
used by the code action to suggest the correct text. -/
structure Failure where
  catName : Name
  actual : Array (String × String)
  deriving TypeName

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
Returns the actual `(before, after)` texts and whether the pair matched. -/
private def comparePair (text : FileMap) (edit : Lsp.TextEdit)
    (pairStx : TSyntax `AssertSuggests.suggestionPair) (idx : Nat)
    : CommandElabM ((String × String) × Bool) := do
  let `(suggestionPair| $before => $after) := pairStx | throwError "unexpected suggestionPair syntax"
  let actualBefore := getOldText text edit.range
  let actualAfter := edit.newText
  let beforeOk ← checkReprint before.raw actualBefore "before" idx
  let afterOk ← checkReprint after.raw actualAfter "after" idx
  return ((actualBefore, actualAfter), beforeOk && afterOk)

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
    let edits ← runAndCollectEdits cmd (linterName?.map (·.getId))
    let text ← getFileMap
    let pairStxs := pairs.getElems
    let catName ← if h : 0 < pairStxs.size then
        match pairStxs[0] with
        | `(suggestionPair| $before => $_) => liftTermElabM (getQuotKind before)
        | _ => pure `tactic
      else pure `tactic
    if edits.size != pairStxs.size then
      let actualPairs := edits.map fun edit =>
        (getOldText text edit.range, edit.newText)
      logErrorAt stx m!"expected {pairStxs.size} suggestion(s) but got {edits.size}"
      pushInfoLeaf (.ofCustomInfo {
        stx := stx, value := Dynamic.mk (Failure.mk catName actualPairs) })
      return
    let results ← (edits.zip pairStxs).mapIdxM fun idx (edit, pairStx) =>
      comparePair text edit pairStx (idx + 1)
    let actualPairs := results.map (·.1)
    unless results.all (·.2) do
      pushInfoLeaf (.ofCustomInfo {
        stx := stx, value := Dynamic.mk (Failure.mk catName actualPairs) })
  | _ => throwUnsupportedSyntax

@[command_elab assertNoSuggestsCmd] def elabAssertNoSuggests : CommandElab
  | stx@`(command| #assertNoSuggests $[$linterName?:ident]? in $cmd) => do
    let edits ← runAndCollectEdits cmd (linterName?.map (·.getId))
    if !edits.isEmpty then
      let text ← getFileMap
      let descriptions := edits.map fun edit =>
        let old := getOldText text edit.range
        s!"  `{old.trim}` => `{edit.newText.trim}`"
      logErrorAt stx
        m!"expected no suggestions but got {edits.size}:\n{"\n".intercalate descriptions.toList}"
  | _ => throwUnsupportedSyntax

open CodeAction Server RequestM in
@[command_code_action assertSuggestsCmd]
def assertSuggestsCodeAction : CommandCodeAction := fun _ _ _ node => do
  let .node _ ts := node | return #[]
  let res := ts.findSome? fun
    | .node (.ofCustomInfo { stx, value }) _ => do
      let f ← value.get? Failure; return (stx, f.catName, f.actual)
    | _ => none
  let some (stx, catName, actual) := res | return #[]
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
      let some tail := stx.getTailPos? true | return eager
      let pairsText := actual.toList.map fun (before, after) =>
        s!"`({catName}| {before.trim}) => `({catName}| {after.trim})"
      let newText := if actual.isEmpty then
        "#assertSuggests in "
      else
        s!"#assertSuggests {", ".intercalate pairsText} in "
      pure { eager with
        edit? := some <| .ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
          newText
        }
      }
  }]

end AssertSuggests
