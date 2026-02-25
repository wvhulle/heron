import Heron.Provider.Transform
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron.Provider

class Refactor (α : Type) extends Transform α

/-- Data pushed into the info tree by `emitSuggestion` so the generic
`heronRefactorProvider` can offer code actions without per-rule providers. -/
structure RefactorSuggestion where
  ruleName : Name
  edit : Lsp.TextEdit
  deriving TypeName

/-- Push a suggestion to the info tree without emitting a diagnostic.

Pushes `TryThisInfo` (used by test macros like `#assertEdits`) and
`RefactorSuggestion` (used by the generic `heronRefactorProvider`). -/
def emitSuggestion (sourceNode replacementNode : Syntax)
    (ruleName : Name) (hintMsg : MessageData) (replacementText : String)
    : CommandElabM Unit := do
  let sugg : Hint.Suggestion :=
    { suggestion := replacementText
      span? := some replacementNode }
  let _ ← liftCoreM <|
    MessageData.hint hintMsg #[sugg] (ref? := some sourceNode)
  let fileMap ← getFileMap
  let refStx := sugg.span?.getD sourceNode
  if let some range := refStx.getRange? then
    let lspRange := fileMap.utf8RangeToLspRange range
    pushInfoLeaf (.ofCustomInfo {
      stx := sourceNode
      value := Dynamic.mk (RefactorSuggestion.mk ruleName { range := lspRange, newText := replacementText })
    })

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
          (Transform.ruleName (α := α))
          (Transform.hintMessage (α := α))
          (Transform.replacementText (α := α) fixData)

def Refactor.addLinter [Refactor α] : IO Unit :=
  lintersRef.modify (·.push (Refactor.toLinter (α := α)))

def Refactor.register [Refactor α] : IO Unit := do
  Transform.initOption (α := α)
  Refactor.addLinter (α := α)

macro "register_refactor" α:ident : command => do
  let a ← `(command| initialize Refactor.register (α := $α))
  let b ← `(command| #eval Refactor.addLinter (α := $α))
  return ⟨mkNullNode #[a, b]⟩

open Server RequestM Lsp in
@[code_action_provider]
def heronRefactorProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let startPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  let suggestions := snap.infoTree.foldInfo (init := #[]) fun _ctx info acc =>
    match info with
    | .ofCustomInfo { stx, value } =>
      match value.get? RefactorSuggestion with
      | some sugg =>
        match stx.getPos? true, stx.getTailPos? true with
        | some head, some tail =>
          if head ≤ endPos && startPos ≤ tail then acc.push sugg else acc
        | _, _ => acc
      | none => acc
    | _ => acc
  let mut actions : Array LazyCodeAction := #[]
  for sugg in suggestions do
    let fullAction : CodeAction := {
      title := s!"Apply: {sugg.ruleName}"
      kind? := "refactor"
      edit? := some <| .ofTextEdit doc.versionedIdentifier sugg.edit
    }
    actions := actions.push {
      eager := { fullAction with edit? := none }
      lazy? := some (pure fullAction)
    }
  return actions

end Heron.Provider
