import Heron.Provider.Transform
import Lean.Server.CodeActions.Basic
import Lean.Compiler.InitAttr

open Lean Elab Command Meta

namespace Heron.Provider

open Server Lsp in
class Refactor (α : Type) extends Transform α where
  /-- Lazy code action provider that computes refactoring suggestions from the
  elaboration snapshot. This runs at request time when the user opens the code
  action menu, not during linting. -/
  codeActions : CodeActionParams → Snapshots.Snapshot → RequestM (Array LazyCodeAction)

/-- Push a suggestion to the info tree without emitting a diagnostic.

Calls `MessageData.hint` which pushes `TryThisInfo` as used by test macros
like `#assertEdits`. -/
def emitSuggestion (sourceNode replacementNode : Syntax)
    (hintMsg : MessageData) (replacementText : String)
    : CommandElabM Unit := do
  let sugg : Hint.Suggestion :=
    { suggestion := replacementText
      span? := some replacementNode }
  let _ ← liftCoreM <|
    MessageData.hint hintMsg #[sugg] (ref? := some sourceNode)

def Refactor.toLinter [Refactor α] : Linter where
  run :=
    withSetOptionIn fun stx => do
      let opt := Transform.option (α := α)
      unless opt.get (← getOptions) do return
      if isReelaborating (← getOptions) then return
      for fixData in ← Transform.detect (α := α) stx do
        emitSuggestion
          (Transform.sourceNode (α := α) fixData)
          (Transform.replacementNode (α := α) fixData)
          (Transform.hintMessage (α := α))
          (Transform.replacementText (α := α) fixData)

def Refactor.addLinter [Refactor α] : IO Unit :=
  lintersRef.modify (·.push (Refactor.toLinter (α := α)))

def Refactor.register [Refactor α] : IO Unit := do
  Transform.initOption (α := α)
  Refactor.addLinter (α := α)

/-- Attribute handler: build `@[init]` aux decls for the linter and register
the instance's `codeActions` as a `@[code_action_provider]`. -/
private unsafe def refactorRuleHandler (declName : Name) : AttrM Unit := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError "@[refactor_rule]: unknown declaration '{declName}'"
  let some αExpr := info.type.getAppArgs[0]?
    | throwError "@[refactor_rule]: expected type of the form `Refactor α`"
  let inst := mkConst declName
  let auxType := mkApp (mkConst ``IO) (mkConst ``Unit)
  -- Determine universe level params for Refactor functions
  let some regInfo := env.find? ``Refactor.register | throwError "Refactor.register not found"
  let levels := regInfo.levelParams.map fun _ => Level.zero
  -- Aux decl 1: calls `register` (initOption + addLinter), tagged @[init] for import
  let registerName := declName ++ `_rule_init
  addAndCompile <| .defnDecl {
    name := registerName, levelParams := [], type := auxType
    value := mkApp2 (mkConst ``Refactor.register levels) αExpr inst
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
    value := mkApp2 (mkConst ``Refactor.addLinter levels) αExpr inst
    hints := .opaque, safety := .unsafe
  }
  let addFn ← IO.ofExcept <| (← getEnv).evalConst (IO Unit) {} linterName
  addFn
  -- Aux decl 3: CodeActionProvider delegating to `Refactor.codeActions`
  let providerName := declName ++ `_rule_provider
  let providerType := mkConst ``Server.CodeActionProvider
  addAndCompile <| .defnDecl {
    name := providerName, levelParams := [], type := providerType
    value := mkApp2 (mkConst ``Refactor.codeActions levels) αExpr inst
    hints := .opaque, safety := .unsafe
  }
  modifyEnv (Server.codeActionProviderExt.addEntry · providerName)

initialize _refactorRuleAttr : TagAttribute ←
  registerTagAttribute `refactor_rule
    "Register a Refactor instance as a heron linter rule and code action provider."
    (validate := unsafe refactorRuleHandler)
    (applicationTime := .afterCompilation)

end Heron.Provider
