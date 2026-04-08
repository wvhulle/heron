import Heron.Rule
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron

/-- Category classifying the kind of pattern a check reports. -/
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

/-- A reference to external documentation that justifies a check rule. -/
structure Reference where
  /-- Short topic description shown in parentheses, e.g. `` `rfl` tactic ``. -/
  topic : String
  /-- URL to the external documentation. -/
  url : String

class Check (α : Type) extends Rule α where
  /-- Diagnostic severity. -/
  severity : MessageSeverity
  /-- What kind of pattern this rule detects. -/
  category : Category
  /-- Syntax node whose range is underlined in the diagnostic. -/
  node : α → Syntax
  /-- LSP diagnostic tags (e.g. unnecessary, deprecated) applied to the match range. -/
  tags : Array Lsp.DiagnosticTag := #[]
  /-- Detailed explanation shown in hover popup. -/
  explanation : α → MessageData := fun _ => m!""
  /-- Optional reference rendered as a markdown link in the hover popup. -/
  reference : Option Reference := none

/-- Emit a check diagnostic with an associated quick-fix code action. -/
def emitCheck (node : Syntax) (severity : MessageSeverity) (category : Category) (tags : Array Lsp.DiagnosticTag)
    (optName : Name) (message explanation : MessageData) (repls : Array Replacement)
    (reference : Option Reference := none) : CommandElabM Unit := do
  let taggedMsg := MessageData.tagged optName message
  let ref := replaceRef node (← MonadLog.getRef)
  let pos := ref.getPos?.getD 0
  let endPos := ref.getTailPos?.getD pos
  let fileMap ← getFileMap
  let msgData ← addMessageContext taggedMsg
  let severity := if warningAsError.get (← getOptions) && severity == .warning then .error else severity
  let msg : Message :=
    { fileName := ← getFileName
      pos := fileMap.toPosition pos
      endPos := fileMap.toPosition endPos
      keepFullRange := true
      data := msgData
      severity
      diagnosticTags := tags }
  let shortFmt ← liftCoreM message.format
  let editsArr ← repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
  let edits := Json.arr (editsArr.map toJson)
  trace[heron]"  emitting {severity} at {(fileMap.toPosition pos)}: {repls.size} replacement(s)"
  let longFmt ← liftCoreM explanation.format
  let mut bodyParts : Array String := #[]
  if !longFmt.pretty.isEmpty then 
    bodyParts := bodyParts.push longFmt.pretty
  if let some ref := reference then 
    bodyParts := bodyParts.push s! "Lean Reference ({ref.topic }): *{ref.url}*"
  bodyParts := bodyParts.push s! "Disable with `set_option {optName} false`"
  let data :=
    Lean.Json.mkObj
      [("title", .str shortFmt.pretty), ("edits", edits), ("hoverTitle", .str shortFmt.pretty),
        ("hoverTags", Json.arr #[toJson (toString category)]),
        ("hoverBody", .str ("\n\n".intercalate bodyParts.toList))]
  let msg := { msg with diagnosticData? := some data.compress }
  logMessage msg

def Check.toLinter [Check α] : Linter where
  name := Rule.ruleName (α := α)
  run :=
    withSetOptionIn fun stx =>
      Rule.runIfEnabled (α := α) stx fun m => do
        emitCheck (Check.node (α := α) m) (Check.severity (α := α)) (Check.category (α := α)) (Check.tags (α := α))
            (Rule.option (α := α)).name (Rule.message (α := α) m) (Check.explanation (α := α) m)
            (← Rule.replacements (α := α) m) (Check.reference (α := α))

def Check.addLinter [Check α] : IO Unit :=
  let name := Rule.ruleName (α := α)
  lintersRef.modify fun linters => (linters.filter (·.name != name)).push (Check.toLinter (α := α))

def Check.registerRunner [Check α] : IO Unit :=
  Rule.registerRunner (α := α)

def Check.register [Check α] : IO Unit := do
  Rule.initOption (α := α)
  Check.registerRunner (α := α)
  Check.addLinter (α := α)

private unsafe def checkRuleHandler :=
  ruleHandlerCore "check_rule" ``Check.register #[``Check.addLinter, ``Check.registerRunner]

initialize _checkRuleAttr : TagAttribute ←
  registerTagAttribute `check_rule "Register a Check instance as a heron linter rule." (validate :=
      unsafe checkRuleHandler) (applicationTime := .afterCompilation)

open Server RequestM Lsp in
@[code_action_provider]
def heronCheckFixProvider : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let mut actions : Array LazyCodeAction := #[]
  for diag in params.context.diagnostics do
    let some data := diag.data? |
      continue
    let some title := data.getObjValAs? String "title" |>.toOption |
      continue
    let some edits := data.getObjValAs? (Array TextEdit) "edits" |>.toOption |
      continue
    let fullAction : CodeAction :=
      { title
        kind? := "quickfix"
        edit? := some <| .ofTextDocumentEdit { textDocument := doc.versionedIdentifier, edits }
        diagnostics? := some #[diag] }
    actions :=
      actions.push
        { eager := { fullAction with edit? := none }
          lazy? := some (pure fullAction) }
  return actions

end Heron
