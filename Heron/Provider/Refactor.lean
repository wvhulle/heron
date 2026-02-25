import Heron.Provider.Transform

open Lean Elab Command Meta

namespace Heron.Provider

class Refactor (α : Type) extends Transform α

/-- Push a suggestion to the info tree without emitting a diagnostic.

Calls `MessageData.hint` which pushes `TryThisInfo` via `pushInfoLeaf` as a
side effect. No message is logged — the `TryThisInfo` is only used by test
macros (`#assertEdits`) which collect info trees from linter execution.

In the LSP, refactor code actions are computed lazily by a
`@[code_action_provider]` registered in each rule file. -/
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

macro "register_refactor" α:ident : command => do
  let a ← `(command| initialize Refactor.register (α := $α))
  let b ← `(command| #eval Refactor.addLinter (α := $α))
  return ⟨mkNullNode #[a, b]⟩

end Heron.Provider
