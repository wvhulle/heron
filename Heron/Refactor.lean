module

public meta import Heron.Rule
public meta import Lean.Server.CodeActions.Basic

public section

open Lean Elab Command Meta

namespace Heron

open Server Lsp in
class Refactor (α : Type) extends Rule α where
  codeActionKind : String := "refactor"

meta def Refactor.activateTestRunner [Refactor α] : IO Unit :=
  Rule.activateTestRunner (α := α)

meta def Refactor.activate [Refactor α] : IO Unit :=
  Refactor.activateTestRunner (α := α)

meta def Refactor.registerAll [Refactor α] (srcMod : Name) : IO Unit := do
  Rule.registerLinterOption (α := α)
  Refactor.activate (α := α)
  Rule.registerSourceModule (α := α) srcMod

open Server RequestM Lsp in
meta def Refactor.toCodeActionProvider [Refactor α] : CodeActionProvider :=
  fun params snap => do
    let doc ← readDoc
    let text := doc.meta.text
    let startPos := text.lspPosToUtf8Pos params.range.start
    let endPos := text.lspPosToUtf8Pos params.range.end
    let name := Rule.name (α := α)
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

private meta unsafe def refactorRuleHandler :=
  handleRuleAttribute "refactor_rule" ``Refactor.registerAll ``Refactor.activate
    (extraSetup := fun declName αExpr inst => do
      let providerName ← mkAuxDeclName (kind := `_rule_provider)
      let value ← Meta.MetaM.run' <|
        Meta.mkAppOptM ``Refactor.toCodeActionProvider #[some αExpr, some inst]
      addAndCompile <| .defnDecl {
        name := providerName, levelParams := []
        type := mkConst ``Server.CodeActionProvider
        value
        hints := .opaque, safety := .unsafe
      }
      modifyEnv (Server.codeActionProviderExt.addEntry · providerName))

meta initialize _refactorRuleAttr : TagAttribute ←
  registerTagAttribute `refactor_rule
    "Register a Refactor instance as a code action provider."
    (validate := unsafe refactorRuleHandler)
    (applicationTime := .afterCompilation)

end Heron
