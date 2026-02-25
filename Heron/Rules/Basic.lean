import Heron.AssertSuggests
import Heron.AssertEdits
import Heron.AssertNoSuggests
import Lean.Meta.Hint
import Lean.PrettyPrinter
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron.Rules

/-- Internal option to prevent recursive linter invocation during re-elaboration. -/
private def heronReelaborating : Lean.Option Bool :=
  { name := `heron.reelaborating, defValue := false }

initialize
  Lean.registerOption `heron.reelaborating {
    defValue := .ofBool false
    descr := "Internal: set during re-elaboration to prevent recursive linter invocation."
    name := `heron
  }

class Rule (α : Type) where
  /-- Rule name, used to derive the linter option `linter.<name>`. -/
  ruleName : Name
  /-- Detect violations, returning typed fix data. -/
  detect : Syntax → CommandElabM (Array α)
  /-- Syntax node to underline in the diagnostic. -/
  diagnosticNode : α → Syntax
  /-- Hint message shown alongside the suggestion widget. -/
  hintMessage : MessageData
  /-- Main diagnostic message shown as the linter warning. -/
  diagnosticMessage : MessageData
  /-- Replacement text for the fix. -/
  replacementText : α → String
  /-- Syntax node whose range is replaced by `replacementText`. -/
  replacementNode : α → Syntax
  /-- Diagnostic severity. -/
  severity : MessageSeverity
  /-- LSP diagnostic tags (e.g. unnecessary, deprecated). -/
  diagnosticTags : Array Lsp.DiagnosticTag := #[]

def Rule.option [Rule α] : Lean.Option Bool :=
  { name := `linter ++ Rule.ruleName (α := α), defValue := false }

def Rule.toLinter [Rule α] : Linter where
  run :=
    withSetOptionIn fun stx => do
      let opt := Rule.option (α := α)
      unless opt.get (← getOptions) do return
      if heronReelaborating.get (← getOptions) then return
      for fixData in ← Rule.detect (α := α) stx do
        let sugg : Hint.Suggestion :=
          { suggestion := Rule.replacementText (α := α) fixData
            span? := some (Rule.replacementNode (α := α) fixData) }
        let diagNode := Rule.diagnosticNode (α := α) fixData
        let hint ← liftCoreM <|
          MessageData.hint (Rule.hintMessage (α := α)) #[sugg]
        let disable := MessageData.note m!"This linter can be disabled with `set_option {opt.name} false`"
        let taggedMsg := MessageData.tagged opt.name
          m!"{(Rule.diagnosticMessage (α := α)) ++ hint}{disable}"
        let ref := replaceRef diagNode (← MonadLog.getRef)
        let pos := ref.getPos?.getD 0
        let endPos := ref.getTailPos?.getD pos
        let fileMap ← getFileMap
        let msgData ← addMessageContext taggedMsg
        let severity : MessageSeverity :=
          if warningAsError.get (← getOptions) && Rule.severity (α := α) == .warning
          then .error else Rule.severity (α := α)
        let msg : Message := {
          fileName := ← getFileName
          pos := fileMap.toPosition pos
          endPos := fileMap.toPosition endPos
          data := msgData
          severity
          diagnosticTags := Rule.diagnosticTags (α := α)
        }
        let refStx := sugg.span?.getD diagNode
        let msg := match refStx.getRange? with
          | some range =>
            let lspRange := fileMap.utf8RangeToLspRange range
            let newText := match sugg.suggestion with
              | .string s => s
              | .tsyntax t => t.raw.reprint.getD ""
            let data := Lean.Json.mkObj [
              ("title", .str s!"Apply: {Rule.ruleName (α := α)}"),
              ("edit", toJson ({ range := lspRange, newText : Lsp.TextEdit }))
            ]
            { msg with diagnosticData? := some data.compress }
          | none => msg
        logMessage msg

def Rule.initOption [Rule α] : IO Unit :=
  Lean.registerOption (`linter ++ Rule.ruleName (α := α))
    { defValue := .ofBool false
      descr := s! "Enable the {Rule.ruleName (α := α)} linter rule."
      name := `linter }

def Rule.addLinter [Rule α] : IO Unit :=
  lintersRef.modify (·.push (Rule.toLinter (α := α)))

/-- Re-elaborate a command collecting info trees.

Uses the scoped `heron.reelaborating` option instead of clearing the global
`lintersRef` to prevent recursive linter invocation. This is safe under
concurrent (async) elaboration — `withScope` modifies only the current
command's options, so other commands' linters are unaffected. -/
def collectElabInfoTrees (stx : Syntax) : CommandElabM (Array InfoTree) := do
  let savedInfoState ← getInfoState
  let savedMessages := (← get).messages
  setInfoState { enabled := true, trees := { } }
  try
    withoutModifyingEnv do
        withScope (fun scope =>
          let opts := heronReelaborating.set (Elab.async.set scope.opts false) true
          { scope with opts }) do
            withReader ({ · with snap? := none }) do
                elabCommand stx
  catch _ =>
    pure ()
  let trees := (← getInfoState).trees.toArray
  setInfoState savedInfoState
  modify fun s => { s with messages := savedMessages }
  return trees

/-- Extract `(ContextInfo × TermInfo)` pairs from an info tree. -/
def collectTermInfos (tree : InfoTree) : Array (ContextInfo × TermInfo) :=
  tree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofTermInfo ti => acc.push (ctx, ti)
    | _ => acc

/-- Run `MetaM` inside a `ContextInfo` context. -/
def runInfoMetaM (ci : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
  match ← (ci.runMetaM lctx x).toBaseIO with
  | .ok a =>
    return a
  | .error e =>
    throwError "{e}"

/-- Deduplicate term infos sharing a start position, keeping the most applied. -/
def deduplicateByPosition (usages : Array (ContextInfo × TermInfo)) : Array (ContextInfo × TermInfo) :=
  usages.foldl (init := #[]) fun acc (ci, ti) =>
    match ti.stx.getPos? true with
    | some pos =>
      let dominated :=
        acc.any fun (_, old) => old.stx.getPos? true == some pos && old.expr.getAppNumArgs >= ti.expr.getAppNumArgs
      if dominated then acc
      else
        let acc :=
          acc.filter fun (_, old) =>
            !(old.stx.getPos? true == some pos && old.expr.getAppNumArgs < ti.expr.getAppNumArgs)
        acc.push (ci, ti)
    | none => acc

/-- Check if an expression references its own name (recursive). -/
def isRecursive (value : Expr) (name : Name) : Bool :=
  value.find? (fun e => e.isConst && e.constName? == some name) |>.isSome

/-- Create a `Syntax` spanning two syntax nodes. -/
def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

/-- Find the `declId` node in a command syntax tree. -/
partial def findDeclId? : Syntax → Option Syntax
  | stx@(.node _ kind args) =>
    if kind == ``Lean.Parser.Command.declId then some stx
    else args.findSome? findDeclId?
  | _ => none

/-- Get the source range of the `declId` in a command, if any. -/
def getDeclIdRange? (stx : Syntax) : Option Syntax.Range :=
  (findDeclId? stx).bind (·.getRange?)

/-- Check whether a `TermInfo` lies outside the declaration-id range. -/
def outsideDeclId (declRange? : Option Syntax.Range) (ti : TermInfo) : Bool :=
  match declRange?, ti.stx.getPos? with
  | some r, some p => !r.contains p
  | _, _ => true

/-- Pretty-print an expression inside a `ContextInfo`, returning a parenthesised string. -/
def ppExprFix? (ci : ContextInfo) (lctx : LocalContext) (e : Expr)
    : CommandElabM (Option String) := do
  try
    let fmt ← runInfoMetaM ci lctx (ppExpr e)
    return some s!"({fmt})"
  catch _ => return none

open Server RequestM Lsp in
@[code_action_provider]
def heronFixProvider : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let mut actions : Array LazyCodeAction := #[]
  for diag in params.context.diagnostics do
    let some data := diag.data? | continue
    let some title := data.getObjValAs? String "title" |>.toOption | continue
    let some edit := (do
      let ej ← data.getObjVal? "edit" |>.toOption
      fromJson? (α := TextEdit) ej |>.toOption) | continue
    let fullAction : CodeAction := {
      title
      kind? := "quickfix"
      edit? := some <| .ofTextEdit doc.versionedIdentifier edit
      diagnostics? := some #[diag]
    }
    actions := actions.push {
      eager := { fullAction with edit? := none }
      lazy? := some (pure fullAction)
    }
  return actions

end Heron.Rules
