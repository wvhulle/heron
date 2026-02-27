import Heron.Transform
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron

open Server Lsp in
class Refactor (α : Type) extends Transform α where
  codeActionKind : String := "refactor"

/-- Push a suggestion to the info tree without emitting a diagnostic.

Calls `MessageData.hint` which pushes `TryThisInfo` as used by test macros
like `#assertRefactor`. -/
def emitSuggestion (hintMsg : MessageData) (repls : Array Replacement)
    : CommandElabM Unit := do
  let some anchor := repls[0]?.map (·.sourceNode) | return
  let _ ← liftCoreM <|
    MessageData.hint hintMsg (repls.map (·.toSuggestion)) (ref? := some anchor)

def Refactor.toLinter [Refactor α] : Linter where
  name := Transform.ruleName (α := α)
  run :=
    withSetOptionIn fun stx =>
      Transform.runIfEnabled (α := α) stx fun fixData =>
        emitSuggestion
          (Transform.shortInstruction (α := α) fixData)
          (Transform.replacements (α := α) fixData)

def Refactor.addLinter [Refactor α] : IO Unit :=
  let name := Transform.ruleName (α := α)
  lintersRef.modify fun linters =>
    (linters.filter (·.name != name)).push (Refactor.toLinter (α := α))

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
        let fmt ← liftCoreM (Transform.shortInstruction (α := α) fd).format
        return FixWithTitle.mk fd fmt.pretty
    let mut actions : Array LazyCodeAction := #[]
    for { fixData, title } in fixes do
      let repls := Transform.replacements (α := α) fixData
      unless repls.any (fun r => match r.sourceNode.getRange? with
        | some range => range.start ≤ endPos && startPos ≤ range.stop
        | none => false) do continue
      let kind := Refactor.codeActionKind (α := α)
      let textEdits := repls.filterMap (·.toTextEdit? text)
      actions := actions.push {
        eager := { title, kind? := kind }
        lazy? := some (pure {
          title, kind? := kind
          edit? := some <| .ofTextDocumentEdit
            { textDocument := doc.versionedIdentifier, edits := textEdits }
        })
      }
    return actions

private unsafe def refactorRuleHandler :=
  ruleHandlerCore "refactor_rule" ``Refactor.register ``Refactor.addLinter
    (extraSetup := fun declName αExpr inst => do
      let env ← getEnv
      let some regInfo := env.find? ``Refactor.toCodeActionProvider
        | throwError "Refactor.toCodeActionProvider not found"
      let levels := regInfo.levelParams.map fun _ => Level.zero
      let providerName := declName ++ `_rule_provider
      addAndCompile <| .defnDecl {
        name := providerName, levelParams := []
        type := mkConst ``Server.CodeActionProvider
        value := mkApp2 (mkConst ``Refactor.toCodeActionProvider levels) αExpr inst
        hints := .opaque, safety := .unsafe
      }
      modifyEnv (Server.codeActionProviderExt.addEntry · providerName))

initialize _refactorRuleAttr : TagAttribute ←
  registerTagAttribute `refactor_rule
    "Register a Refactor instance as a heron linter rule and code action provider."
    (validate := unsafe refactorRuleHandler)
    (applicationTime := .afterCompilation)

end Heron
