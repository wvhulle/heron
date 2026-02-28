import Heron.Transform
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron

/-- Category classifying the kind of violation a diagnostic reports. -/
inductive Category where
  | style
  | simplification
  | performance
  | correctness
  deriving Inhabited, BEq

instance : ToString Category where
  toString
    | .style => "style"
    | .simplification => "simplification"
    | .performance => "performance"
    | .correctness => "correctness"

/-- A reference to external documentation that justifies a diagnostic rule. -/
structure Reference where
  /-- Short topic description shown in parentheses, e.g. `` `rfl` tactic ``. -/
  topic : String
  /-- URL to the external documentation. -/
  url : String

class Diagnostic (α : Type) extends Transform α where
  /-- Diagnostic severity. -/
  severity : MessageSeverity
  /-- What kind of violation this rule detects. -/
  category : Category
  /-- Syntax node whose range is underlined in the diagnostic. -/
  violationNode : α → Syntax
  /-- LSP diagnostic tags (e.g. unnecessary, deprecated) applied to the violation range. -/
  diagnosticTags : Array Lsp.DiagnosticTag := #[]
  /-- Detailed explanation shown in hover popup. -/
  longInstruction : α → MessageData := fun _ => m!""
  /-- Optional reference rendered as a markdown link in the hover popup. -/
  officialReference : Option Reference := none

/-- Emit a diagnostic message with an associated quick-fix code action. -/
def emitDiagnostic (violationNode : Syntax)
    (severity : MessageSeverity)
    (category : Category)
    (diagnosticTags : Array Lsp.DiagnosticTag)
    (optName : Name)
    (shortInstruction longInstruction : MessageData) (repls : Array Replacement)
    (officialReference : Option Reference := none)
    : CommandElabM Unit := do
  let _ ← liftCoreM <|
    MessageData.hint shortInstruction (repls.map (·.toSuggestion))
  let taggedMsg := MessageData.tagged optName shortInstruction
  let ref := replaceRef violationNode (← MonadLog.getRef)
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
  let shortFmt ← liftCoreM shortInstruction.format
  let edits := (repls.filterMap (·.toTextEdit? fileMap)).map toJson
  -- Structured hover data
  let longFmt ← liftCoreM longInstruction.format
  let mut bodyParts : Array String := #[]
  if !longFmt.pretty.isEmpty then
    bodyParts := bodyParts.push longFmt.pretty
  if let some ref := officialReference then
    bodyParts := bodyParts.push s!"Lean Reference ({ref.topic}): *{ref.url}*"
  bodyParts := bodyParts.push s!"Disable with `set_option {optName} false`"
  let data := Lean.Json.mkObj [
    ("title", .str shortFmt.pretty),
    ("edits", Json.arr edits),
    ("hoverTitle", .str shortFmt.pretty),
    ("hoverTags", Json.arr #[toJson (toString category)]),
    ("hoverBody", .str ("\n\n".intercalate bodyParts.toList))
  ]
  let msg := { msg with diagnosticData? := some data.compress }
  logMessage msg

def Diagnostic.toLinter [Diagnostic α] : Linter where
  name := Transform.ruleName (α := α)
  run :=
    withSetOptionIn fun stx =>
      Transform.runIfEnabled (α := α) stx fun fixData => do
        emitDiagnostic (Diagnostic.violationNode (α := α) fixData)
          (Diagnostic.severity (α := α))
          (Diagnostic.category (α := α))
          (Diagnostic.diagnosticTags (α := α))
          (Transform.option (α := α)).name
          (Transform.shortInstruction (α := α) fixData)
          (Diagnostic.longInstruction (α := α) fixData)
          (Transform.replacements (α := α) fixData)
          (Diagnostic.officialReference (α := α))

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
