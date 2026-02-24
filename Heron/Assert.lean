import Lean.Elab.Command
import Lean.Elab.Quotation
import Lean.Server.InfoUtils
import Lean.Server.CodeActions
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

structure SuggestionMismatch where
  catName : Name
  linterName? : Option Name
  actualEdits : Array SuggestionEdit
  deriving TypeName

def pushMismatchToInfoTree (stx : Syntax) (catName : Name) (linterName? : Option Name)
    (actualEdits : Array SuggestionEdit) : CommandElabM Unit :=
  pushInfoLeaf (.ofCustomInfo { stx, value := Dynamic.mk (SuggestionMismatch.mk catName linterName? actualEdits) })

def renderAssertSuggestsPrefix (catName : Name) (linterName? : Option Name)
    (actualEdits : Array SuggestionEdit) : String :=
  let linterPrefix := linterName?.elim "" (s!"{·} ")
  if actualEdits.isEmpty then
    s!"#assertSuggests {linterPrefix}"
  else
    let formattedPairs := actualEdits.map fun { before, after } =>
      s!"`({catName}| {before.trimAscii}) => `({catName}| {after.trimAscii})"
    s!"#assertSuggests {linterPrefix}{", ".intercalate formattedPairs.toList} "

syntax suggestionPair := term " => " term

private def verifyReprintedQuotation (quotStx : Syntax) (actual : String) (label : String) (idx : Nat)
    : CommandElabM Bool := do
  match quotStx.getQuotContent.reprint with
  | some expectedText =>
    if expectedText.trimAscii == actual.trimAscii then return true
    logErrorAt quotStx
      m!"{label} mismatch for suggestion {idx}:\n  expected: {expectedText.trimAscii}\n  actual:   {actual.trimAscii}"
    return false
  | none =>
    logWarningAt quotStx m!"could not reprint expected {label} syntax for suggestion {idx}"
    return false

def verifySuggestionPair (text : FileMap) (edit : Lsp.TextEdit)
    (pairStx : TSyntax `Heron.Assert.suggestionPair) (idx : Nat)
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
    name := `Heron.Assert.restoreLinters
  }]

private def runAllLintersCollectTrees (cmd : Syntax) : CommandElabM (Array InfoTree) :=
  withoutModifyingEnv do
    let linters ← lintersRef.get
    linters.foldlM (init := #[]) fun acc linter =>
      return acc ++ (← runLinterAndCollectTrees linter cmd).toArray

def elabCommandAndCollectSuggestionEdits (cmd : Syntax) (linterName? : Option Name := none)
    : CommandElabM (Array Lsp.TextEdit) := do
  let enableLinterScope := linterName?.elim id fun name (scope : Scope) =>
    { scope with opts := scope.opts.insert (`linter ++ name) (.ofBool true) }
  withScope enableLinterScope do
    let collectedTrees ← withInfoCollectionDisabled do
      elabCommandSilently cmd
      runAllLintersCollectTrees cmd
    modify fun s => { s with messages := .empty }
    scheduleLinterRestore
    return collectTryThisEdits collectedTrees

end Heron.Assert
