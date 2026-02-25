import Lean.Elab.Command
import Lean.Meta.Hint

open Lean Elab Command Meta

namespace Heron

/-- Push a suggestion to the info tree without emitting a diagnostic.

Calls `MessageData.hint` which pushes `TryThisInfo` via `pushInfoLeaf` as a
side effect. No message is logged — the `TryThisInfo` is only used by test
macros (`#assertEdits`) which collect info trees from linter execution.

In the LSP, refactor code actions are computed lazily by a
`@[code_action_provider]` registered in each rule file. -/
def emitSuggestion (diagNode replacementNode : Syntax)
    (hintMsg : MessageData) (replacementText : String)
    : CommandElabM Unit := do
  let sugg : Hint.Suggestion :=
    { suggestion := replacementText
      span? := some replacementNode }
  let _ ← liftCoreM <|
    MessageData.hint hintMsg #[sugg] (ref? := some diagNode)

end Heron
