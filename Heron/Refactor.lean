module

public meta import Heron.Rule
public meta import Lean.Server.CodeActions.Basic

public section

open Lean Elab Command Meta

namespace Heron

open Server Lsp in
class Refactor (α : Type) extends Rule α where
  codeActionKind : String := "refactor"

/-- Register a `Refactor` instance: linter option and test runner.
Code action provider registration is handled by `@[code_action_provider]` in rule files. -/
meta def Refactor.register [Refactor α] : IO Unit := do
  let name := Rule.name (α := α)
  Rule.registerLinterOption name
  Rule.testRunnerRegistry.modify (·.insert name (Rule.buildTestRunner (α := α)))

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
          let detected ← Rule.detectAll (α := α) snap.stx
          detected.mapM fun m => do
            let repls ← Rule.replacements (α := α) m
            let fileMap ← getFileMap
            let textEdits ← repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
            return (Rule.message (α := α) m, repls, textEdits)
    let results ← runCommandElabM snap detectAndReplace
    let kind := Refactor.codeActionKind (α := α)
    let overlaps (r : Replacement) := match r.emphasizedSyntax.getRange? with
      | some range => range.start ≤ endPos && startPos ≤ range.stop
      | none => false
    results.filterMapM fun (msg, repls, textEdits) => do
      unless repls.any overlaps do return none
      if textEdits.isEmpty then return none
      let title := (← msg.format).pretty
      return some {
        eager := { title, kind? := kind }
        lazy? := some (pure {
          title, kind? := kind
          edit? := some <| .ofTextDocumentEdit
            { textDocument := doc.versionedIdentifier, edits := textEdits }
        })
      }

end Heron
