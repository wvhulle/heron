import Heron.Transform
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron

class Diagnostic (α : Type) extends Transform α where
  /-- Main diagnostic message shown as the linter warning. -/
  diagnosticMessage : MessageData
  /-- Diagnostic severity. -/
  severity : MessageSeverity
  /-- LSP diagnostic tags (e.g. unnecessary, deprecated). -/
  diagnosticTags : Array Lsp.DiagnosticTag := #[]

/-- Emit a diagnostic message with an associated quick-fix code action. -/
def emitDiagnostic (sourceNode : Syntax)
    (severity : MessageSeverity) (diagnosticTags : Array Lsp.DiagnosticTag)
    (optName : Name)
    (diagnosticMsg hintMsg : MessageData) (repls : Array Replacement)
    : CommandElabM Unit := do
  let hint ← liftCoreM <|
    MessageData.hint hintMsg (repls.map (·.toSuggestion))
  let disable := MessageData.note m!"This linter can be disabled with `set_option {optName} false`"
  let taggedMsg := MessageData.tagged optName
    m!"{diagnosticMsg ++ hint}{disable}"
  let ref := replaceRef sourceNode (← MonadLog.getRef)
  let pos := ref.getPos?.getD 0
  let endPos := ref.getTailPos?.getD pos
  let fileMap ← getFileMap
  let msgData ← addMessageContext taggedMsg
  let severity :=
    if warningAsError.get (← getOptions) && severity == .warning
    then .error else severity
  let msg : Message := {
    fileName := ← getFileName
    pos := fileMap.toPosition pos
    endPos := fileMap.toPosition endPos
    data := msgData
    severity
    diagnosticTags
  }
  let hintFmt ← liftCoreM hintMsg.format
  let edits := (repls.filterMap (·.toTextEdit? fileMap)).map toJson
  let data := Lean.Json.mkObj [
    ("title", .str hintFmt.pretty),
    ("edits", Json.arr edits)
  ]
  let msg := { msg with diagnosticData? := some data.compress }
  logMessage msg

def Diagnostic.toLinter [Diagnostic α] : Linter where
  name := Transform.ruleName (α := α)
  run :=
    withSetOptionIn fun stx =>
      Transform.runIfEnabled (α := α) stx fun fixData => do
        let repls := Transform.replacements (α := α) fixData
        let some first := repls[0]? | return
        emitDiagnostic first.sourceNode
          (Diagnostic.severity (α := α))
          (Diagnostic.diagnosticTags (α := α))
          (Transform.option (α := α)).name
          (Diagnostic.diagnosticMessage (α := α))
          (Transform.hintMessage (α := α) fixData)
          repls

def Diagnostic.addLinter [Diagnostic α] : IO Unit :=
  let name := Transform.ruleName (α := α)
  lintersRef.modify fun linters =>
    (linters.filter (·.name != name)).push (Diagnostic.toLinter (α := α))

def Diagnostic.register [Diagnostic α] : IO Unit := do
  Transform.initOption (α := α)
  Diagnostic.addLinter (α := α)

private unsafe def diagnosticRuleHandler :=
  ruleHandlerCore "diagnostic_rule" ``Diagnostic.register ``Diagnostic.addLinter

initialize _diagnosticRuleAttr : TagAttribute ←
  registerTagAttribute `diagnostic_rule
    "Register a Diagnostic instance as a heron linter rule."
    (validate := unsafe diagnosticRuleHandler)
    (applicationTime := .afterCompilation)

open Server RequestM Lsp in
@[code_action_provider]
def heronFixProvider : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let mut actions : Array LazyCodeAction := #[]
  for diag in params.context.diagnostics do
    let some data := diag.data? | continue
    let some title := data.getObjValAs? String "title" |>.toOption | continue
    let some edits := data.getObjValAs? (Array TextEdit) "edits" |>.toOption | continue
    let fullAction : CodeAction := {
      title
      kind? := "quickfix"
      edit? := some <| .ofTextDocumentEdit
        { textDocument := doc.versionedIdentifier, edits }
      diagnostics? := some #[diag]
    }
    actions := actions.push {
      eager := { fullAction with edit? := none }
      lazy? := some (pure fullAction)
    }
  return actions

end Heron
