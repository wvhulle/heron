import Heron.Provider.Transform
import Lean.Server.CodeActions.Basic
import Lean.Compiler.InitAttr

open Lean Elab Command Meta

namespace Heron.Provider

open Server Lsp in
class Refactor (α : Type) extends Transform α where
  codeActionKind : String := "refactor"

/-- Push a suggestion to the info tree without emitting a diagnostic.

Calls `MessageData.hint` which pushes `TryThisInfo` as used by test macros
like `#assertEdits`. -/
def emitSuggestion (hintMsg : MessageData) (repls : Array Replacement)
    : CommandElabM Unit := do
  let some anchor := repls[0]?.map (·.sourceNode) | return
  let suggs := repls.map fun r =>
    { suggestion := r.insertText
      span? := some r.targetNode : Hint.Suggestion }
  let _ ← liftCoreM <|
    MessageData.hint hintMsg suggs (ref? := some anchor)

def Refactor.toLinter [Refactor α] : Linter where
  run :=
    withSetOptionIn fun stx => do
      let opt := Transform.option (α := α)
      unless opt.get (← getOptions) do return
      if isReelaborating (← getOptions) then return
      for fixData in ← Transform.detect (α := α) stx do
        emitSuggestion
          (Transform.hintMessage (α := α) fixData)
          (Transform.replacements (α := α) fixData)

def Refactor.addLinter [Refactor α] : IO Unit :=
  lintersRef.modify (·.push (Refactor.toLinter (α := α)))

def Refactor.register [Refactor α] : IO Unit := do
  Transform.initOption (α := α)
  Refactor.addLinter (α := α)

private structure FixWithTitle (α : Type) where
  fixData : α
  title : String

open Server RequestM Lsp in
def Refactor.toCodeActionProvider [Refactor α] : CodeActionProvider :=
  fun params snap => do
    let doc ← readDoc
    let text := doc.meta.text
    let startPos := text.lspPosToUtf8Pos params.range.start
    let endPos := text.lspPosToUtf8Pos params.range.end
    let fixes ← runCommandElabM snap do
      let rawFixes ← Transform.detect (α := α) snap.stx
      rawFixes.mapM fun fd => do
        let fmt ← liftCoreM (Transform.hintMessage (α := α) fd).format
        return FixWithTitle.mk fd fmt.pretty
    let mut actions : Array LazyCodeAction := #[]
    for { fixData, title } in fixes do
      let repls := Transform.replacements (α := α) fixData
      unless repls.any (fun r => match r.sourceNode.getRange? with
        | some range => range.start ≤ endPos && startPos ≤ range.stop
        | none => false) do continue
      let kind := Refactor.codeActionKind (α := α)
      let textEdits := repls.filterMap fun r => do
        let range ← r.targetNode.getRange?
        return { range := text.utf8RangeToLspRange range, newText := r.insertText : Lsp.TextEdit }
      actions := actions.push {
        eager := { title, kind? := kind }
        lazy? := some (pure {
          title, kind? := kind
          edit? := some <| .ofTextDocumentEdit
            { textDocument := doc.versionedIdentifier, edits := textEdits }
        })
      }
    return actions

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
    value := mkApp2 (mkConst ``Refactor.toCodeActionProvider levels) αExpr inst
    hints := .opaque, safety := .unsafe
  }
  modifyEnv (Server.codeActionProviderExt.addEntry · providerName)

initialize _refactorRuleAttr : TagAttribute ←
  registerTagAttribute `refactor_rule
    "Register a Refactor instance as a heron linter rule and code action provider."
    (validate := unsafe refactorRuleHandler)
    (applicationTime := .afterCompilation)

end Heron.Provider
