module

public meta import Heron.Rule
public meta import Heron.Lsp
public meta import Lean.Server.CodeActions.Basic

public section

open Lean Elab Command Meta

namespace Heron

open Server Lsp in
class Refactor (α : Type) extends Rule α where
  codeActionKind : String := "refactor"

open Lsp in
meta def syntaxOverlapsRequest (text : FileMap) (params : CodeActionParams) (stx : Syntax) : Bool :=
  match stx.getRange? with
  | some range =>
    range.start ≤ text.lspPosToUtf8Pos params.range.end && text.lspPosToUtf8Pos params.range.start ≤ range.stop
  | none => false

open Server RequestM Lsp in
meta def Refactor.toCodeActionProvider [Refactor α] : CodeActionProvider :=
  fun params snap => do
    let doc ← readDoc
    let text := doc.meta.text
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
            let repls ← Rule.replacementsFor m
            let fileMap ← getFileMap
            let textEdits ← repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
            return (Rule.message (α := α) m, repls, textEdits)
    let results ← runCommandElabM snap detectAndReplace
    let kind := Refactor.codeActionKind (α := α)
    results.filterMapM fun (msg, repls, textEdits) => do
      unless repls.any (syntaxOverlapsRequest text params ·.emphasizedSyntax) do return none
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

/-- Register a `Refactor` instance: linter option, test runner and code action provider. -/
meta def Refactor.register [Refactor α] : IO Unit := do
  let name := Rule.name (α := α)
  registerLinterOption name
  ruleCatalog.modify fun catalog =>
    catalog.push
      { name
        kind := .refactor
        description := Rule.description (α := α)
        sources := Rule.sources (α := α)
        offersFix := Rule.offersFix (α := α) }
  testRunnerRegistry.modify (·.insert name (buildTestRunner (α := α)))
  Server.addBuiltinCodeActionProvider (lspName (`refactor ++ name))
    (Refactor.toCodeActionProvider (α := α))

end Heron
