import Heron.Provider.Transform
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron.Provider

class Diagnostic (α : Type) extends Transform α where
  /-- Main diagnostic message shown as the linter warning. -/
  diagnosticMessage : MessageData
  /-- Diagnostic severity. -/
  severity : MessageSeverity
  /-- LSP diagnostic tags (e.g. unnecessary, deprecated). -/
  diagnosticTags : Array Lsp.DiagnosticTag := #[]

/-- Emit a diagnostic message with an associated quick-fix code action. -/
def emitDiagnostic (sourceNode replacementNode : Syntax)
    (severity : MessageSeverity) (diagnosticTags : Array Lsp.DiagnosticTag)
    (ruleName : Name) (optName : Name)
    (diagnosticMsg hintMsg : MessageData) (replacementText : String)
    : CommandElabM Unit := do
  let sugg : Hint.Suggestion :=
    { suggestion := replacementText
      span? := some replacementNode }
  let hint ← liftCoreM <|
    MessageData.hint hintMsg #[sugg]
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
  let refStx := sugg.span?.getD sourceNode
  let msg := match refStx.getRange? with
    | some range =>
      let lspRange := fileMap.utf8RangeToLspRange range
      let newText := match sugg.suggestion with
        | .string s => s
        | .tsyntax t => t.raw.reprint.getD ""
      let data := Lean.Json.mkObj [
        ("title", .str s!"Apply: {ruleName}"),
        ("edit", toJson ({ range := lspRange, newText : Lsp.TextEdit }))
      ]
      { msg with diagnosticData? := some data.compress }
    | none => msg
  logMessage msg

def Diagnostic.toLinter [Diagnostic α] : Linter where
  run :=
    withSetOptionIn fun stx => do
      let opt := Transform.option (α := α)
      unless opt.get (← getOptions) do return
      if isReelaborating (← getOptions) then return
      for fixData in ← Transform.detect (α := α) stx do
        emitDiagnostic
          (Transform.sourceNode (α := α) fixData)
          (Transform.replacementNode (α := α) fixData)
          (Diagnostic.severity (α := α))
          (Diagnostic.diagnosticTags (α := α))
          (Transform.ruleName (α := α))
          opt.name
          (Diagnostic.diagnosticMessage (α := α))
          (Transform.hintMessage (α := α))
          (Transform.replacementText (α := α) fixData)

def Diagnostic.addLinter [Diagnostic α] : IO Unit :=
  lintersRef.modify (·.push (Diagnostic.toLinter (α := α)))

def Diagnostic.register [Diagnostic α] : IO Unit := do
  Transform.initOption (α := α)
  Diagnostic.addLinter (α := α)

macro "register_diagnostic" α:ident : command => do
  let a ← `(command| initialize Diagnostic.register (α := $α))
  let b ← `(command| #eval Diagnostic.addLinter (α := $α))
  return ⟨mkNullNode #[a, b]⟩

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

end Heron.Provider
