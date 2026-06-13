import Lean
import Heron

/-! Shared frontend-driving helpers for the elaboration-based engines (`PerFile`, `SharedEnv`):
the per-command detection loop and a bounded-parallel map. A non-`module` file so it can call
Heron's `meta` `collectFixRecords`. -/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Frontend Lean.Parser
open Heron (FixRecord collectFixRecords)

namespace Reporter

/-- Walk a module's commands, gathering a `FixRecord` per suggested edit.

Each command is elaborated **once** (`elabCommandAtFrontend`) — that advances env/scope for later
commands and populates the info trees the two type-aware rules consult — then detection runs after,
reusing those trees. `#eval`/`#eval!` are never elaborated (they run user code); `initialize` is
skipped in imported mode (already present — re-elaborating an imported decl panics). `commitInit`
(growing-env mode) also commits `initialize`, since declarations there are not pre-imported. -/
partial def collectLoop (all commitInit : Bool) (acc : Array FixRecord) : FrontendM (Array FixRecord) := do
  updateCmdPos
  let cmdState ← getCommandState
  let ictx ← getInputContext
  let pstate ← getParserState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts,
                 currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmd, ps, messages) := parseCommand ictx pmctx pstate cmdState.messages
  setParserState ps
  setMessages messages
  let imported := !commitInit
  let isEval := cmd.isOfKind ``Lean.Parser.Command.eval || cmd.isOfKind ``Lean.Parser.Command.evalBang
  let isInit := cmd.isOfKind ``Lean.Parser.Command.initialize
  let acc ← if isEval || (imported && isInit) then pure acc else do
    elabCommandAtFrontend cmd
    let found ← runCommandElabM (collectFixRecords all cmd)
    pure (acc ++ found)
  if isTerminalCommand cmd then return acc else collectLoop all commitInit acc

/-- Run `f` over `xs` with at most `conc` concurrent tasks (`conc = 1` ⇒ sequential), preserving
input order. `f` handles its own errors. -/
partial def parMap {α β : Type} (conc : Nat) (xs : Array α) (f : α → IO β) (i : Nat := 0)
    (acc : Array β := #[]) : IO (Array β) := do
  if i ≥ xs.size then return acc
  let stop := min (i + max 1 conc) xs.size
  let tasks ← (xs.extract i stop).mapM fun x => IO.asTask (f x)
  let mut acc := acc
  for t in tasks do
    match ← IO.wait t with
    | .ok b => acc := acc.push b
    | .error _ => pure ()
  parMap conc xs f stop acc

end Reporter
