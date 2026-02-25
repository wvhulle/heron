import Lean.Elab.Command
import Lean.Elab.Quotation
import Lean.Server.InfoUtils
import Lean.Meta.TryThis

namespace Heron.Assert

open Lean Elab Command Server Meta Tactic.TryThis Term.Quotation

private partial def foldInfoTreeIncludingContextFree (f : Info → α → α) (init : α) : InfoTree → α
  | .context _ t => foldInfoTreeIncludingContextFree f init t
  | .node i ts =>
    let a := f i init
    ts.foldl (init := a) (foldInfoTreeIncludingContextFree f)
  | .hole _ => init

private def collectTryThisEdits (trees : Array InfoTree) : Array Lsp.TextEdit :=
  trees.flatMap fun tree =>
    foldInfoTreeIncludingContextFree (init := #[]) (fun info acc =>
      match info with
      | .ofCustomInfo { value, .. } => (value.get? TryThisInfo).elim acc (acc.push ·.edit)
      | _ => acc) tree

structure SuggestionEdit where
  before : String
  after : String

def lspEditToSuggestionEdit (text : FileMap) (edit : Lsp.TextEdit) : SuggestionEdit :=
  { before := have startPos := text.lspPosToUtf8Pos edit.range.start;
have endPos := text.lspPosToUtf8Pos edit.range.end;
String.Pos.Raw.extract text.source startPos endPos, after := edit.newText }

syntax replacementPair := term " => " term

private def verifyReprintedQuotation (quotStx : Syntax) (actual : String) (label : String) (idx : Nat)
    : CommandElabM Bool := do
  match quotStx.getQuotContent.reprint with
  | some expectedText =>
    if expectedText.trimAscii == actual.trimAscii then return true
    logErrorAt quotStx
      m!"{label} mismatch for replacement {idx}:\n  expected: {expectedText.trimAscii}\n  actual:   {actual.trimAscii}"
    return false
  | none =>
    logWarningAt quotStx m!"could not reprint expected {label} syntax for replacement {idx}"
    return false

def verifyReplacementPair (text : FileMap) (edit : Lsp.TextEdit)
    (pairStx : TSyntax `Heron.Assert.replacementPair) (idx : Nat)
    : CommandElabM Bool := do
  let `(replacementPair| $before => $after) := pairStx | throwError "unexpected replacementPair syntax"
  let beforeOk ← verifyReprintedQuotation before.raw (lspEditToSuggestionEdit text edit).before "before" idx
  let afterOk ← verifyReprintedQuotation after.raw (lspEditToSuggestionEdit text edit).after "after" idx
  return beforeOk && afterOk

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
    name := `Heron.Assert.restoreLinters
  }]

private def runAllLintersCollectTrees (cmd : Syntax) : CommandElabM (Array InfoTree) :=
  withoutModifyingEnv do
    let linters ← lintersRef.get
    linters.foldlM (init := #[]) fun acc linter =>
      return acc ++ (← runLinterAndCollectTrees linter cmd).toArray

def collectReplacements (cmd : Syntax) (linterName : Name)
    : CommandElabM (Array Lsp.TextEdit) := do
  withScope (fun scope => { scope with opts := scope.opts.insert (`linter ++ linterName) (.ofBool true) }) do
    let collectedTrees ← withInfoCollectionDisabled do
      elabCommandSilently cmd
      runAllLintersCollectTrees cmd
    modify fun s => { s with messages := .empty }
    scheduleLinterRestore
    return collectTryThisEdits collectedTrees

end Heron.Assert
