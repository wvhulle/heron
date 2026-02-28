import Heron.Rule
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron

open Server Lsp in
class Refactor (α : Type) extends Rule α where
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
  name := Rule.ruleName (α := α)
  run :=
    withSetOptionIn fun stx =>
      Rule.runIfEnabled (α := α) stx fun m =>
        emitSuggestion
          (Rule.message (α := α) m)
          (Rule.replacements (α := α) m)

def Refactor.addLinter [Refactor α] : IO Unit :=
  let name := Rule.ruleName (α := α)
  lintersRef.modify fun linters =>
    (linters.filter (·.name != name)).push (Refactor.toLinter (α := α))

def Refactor.register [Refactor α] : IO Unit := do
  Rule.initOption (α := α)
  Refactor.addLinter (α := α)

private structure MatchWithTitle (α : Type) where
  matchData : α
  title : String

open Server RequestM Lsp in
def Refactor.toCodeActionProvider [Refactor α] : CodeActionProvider :=
  fun params snap => do
    let doc ← readDoc
    let text := doc.meta.text
    let startPos := text.lspPosToUtf8Pos params.range.start
    let endPos := text.lspPosToUtf8Pos params.range.end
    let results ← runCommandElabM snap do
      let rawResults ← Rule.detect (α := α) snap.stx
      rawResults.mapM fun m => do
        let fmt ← liftCoreM (Rule.message (α := α) m).format
        return MatchWithTitle.mk m fmt.pretty
    let mut actions : Array LazyCodeAction := #[]
    for { matchData, title } in results do
      let repls := Rule.replacements (α := α) matchData
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
