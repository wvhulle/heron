import Heron.Rule
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron

open Server Lsp in
class Refactor (α : Type) extends Rule α where
  codeActionKind : String := "refactor"

def Refactor.registerRunner [Refactor α] : IO Unit :=
  Rule.registerRunner (α := α)

def Refactor.register [Refactor α] : IO Unit := do
  Rule.initOption (α := α)
  Refactor.registerRunner (α := α)

open Server RequestM Lsp in
def Refactor.toCodeActionProvider [Refactor α] : CodeActionProvider :=
  fun params snap => do
    let doc ← readDoc
    let text := doc.meta.text
    let startPos := text.lspPosToUtf8Pos params.range.start
    let endPos := text.lspPosToUtf8Pos params.range.end
    let name := Rule.ruleName (α := α)
    let detectAndReplace : CommandElabM (Array (MessageData × Array Replacement × Array Lsp.TextEdit)) :=
      withTraceNode `heron.profile
          (fun res => return match res with
            | .ok _ => m!"{name}: done"
            | .error e => m!"{name}: error {e.toMessageData}")
          (tag := toString name) do
        withTraceNode `heron.profile.detect
            (fun res => return match res with
              | .ok r => m!"{name} detect: {r.size} match(es)"
              | .error e => m!"{name} detect: error {e.toMessageData}")
            (tag := s!"{name}.detect") do
          let detected ← Rule.detect (α := α) snap.stx
          detected.mapM fun m => do
            let repls ← Rule.replacements (α := α) m
            let fileMap ← getFileMap
            let textEdits ← repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
            return (Rule.message (α := α) m, repls, textEdits)
    let results ← runCommandElabM snap detectAndReplace
    let mut actions : Array LazyCodeAction := #[]
    for (msg, repls, textEdits) in results do
      unless repls.any (fun r => match r.emphasizedSyntax.getRange? with
        | some range => range.start ≤ endPos && startPos ≤ range.stop
        | none => false) do continue
      let kind := Refactor.codeActionKind (α := α)
      let title := (← msg.format).pretty
      if textEdits.isEmpty then continue
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
  ruleHandlerCore "refactor_rule" ``Refactor.register #[``Refactor.registerRunner]
    (extraSetup := fun declName αExpr inst => do
      let some provInfo := (← getEnv).find? ``Refactor.toCodeActionProvider
        | throwError "Refactor.toCodeActionProvider not found"
      let provLevels := provInfo.levelParams.map fun _ => Level.zero
      let providerName := declName ++ `_rule_provider
      addAndCompile <| .defnDecl {
        name := providerName, levelParams := []
        type := mkConst ``Server.CodeActionProvider
        value := mkApp2 (mkConst ``Refactor.toCodeActionProvider provLevels) αExpr inst
        hints := .opaque, safety := .unsafe
      }
      modifyEnv (Server.codeActionProviderExt.addEntry · providerName))

initialize _refactorRuleAttr : TagAttribute ←
  registerTagAttribute `refactor_rule
    "Register a Refactor instance as a code action provider."
    (validate := unsafe refactorRuleHandler)
    (applicationTime := .afterCompilation)

end Heron
