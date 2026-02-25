import Heron.Provider.Transform
import Lean.Server.CodeActions.Basic
import Lean.Compiler.InitAttr

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
    withSetOptionIn fun stx => do
      unless Transform.isEnabled (α := α) (← getOptions) do return
      if isReelaborating (← getOptions) then return
      let optName := (Transform.option (α := α)).name
      for fixData in ← Transform.detect (α := α) stx do
        let repls := Transform.replacements (α := α) fixData
        let some first := repls[0]? | continue
        emitDiagnostic first.sourceNode
          (Diagnostic.severity (α := α))
          (Diagnostic.diagnosticTags (α := α))
          optName
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

/-- Attribute handler: build an `@[init]` aux decl calling `Diagnostic.register`,
then evaluate it immediately so the linter is active in the current file. -/
private unsafe def diagnosticRuleHandler (declName : Name) : AttrM Unit := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError "@[diagnostic_rule]: unknown declaration '{declName}'"
  let some αExpr := info.type.getAppArgs[0]?
    | throwError "@[diagnostic_rule]: expected type of the form `Diagnostic α`"
  let inst := mkConst declName
  let auxType := mkApp (mkConst ``IO) (mkConst ``Unit)
  -- Aux decl 1: calls `register` (initOption + addLinter), tagged @[init] for import
  let registerName := declName ++ `_rule_init
  addAndCompile <| .defnDecl {
    name := registerName, levelParams := [], type := auxType
    value := mkApp2 (mkConst ``Diagnostic.register) αExpr inst
    hints := .opaque, safety := .unsafe
  }
  modifyEnv fun env =>
    match regularInitAttr.setParam env registerName .anonymous with
    | .ok env' => env'
    | .error _ => env
  -- Aux decl 2: calls `addLinter` only, evaluated immediately for current file
  let linterName := declName ++ `_rule_addLinter
  addAndCompile <| .defnDecl {
    name := linterName, levelParams := [], type := auxType
    value := mkApp2 (mkConst ``Diagnostic.addLinter) αExpr inst
    hints := .opaque, safety := .unsafe
  }
  let addFn ← IO.ofExcept <| (← getEnv).evalConst (IO Unit) {} linterName
  addFn

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

end Heron.Provider
