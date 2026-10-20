import Lean
import Heron

/-! Shared frontend-driving helpers for the elaboration-based engines (`PerFile`, `SharedEnv`):
the per-command detection loop and a bounded-parallel map. A non-`module` file so it can call
Heron's `meta` `collectFixRecords`. -/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Frontend Lean.Parser
open Heron (FixRecord RuleEntry collectFixRecords)

namespace FixReporting

def scanOptions : Options := (Elab.async.set ({} : Options) false).setBool `linter.heron true

def selectChecks (registry : Array RuleEntry) (requested : Array Name) :
    Except String (Array RuleEntry) :=
  if requested.isEmpty then .ok registry
  else requested.mapM fun name =>
    match registry.find? (·.name == name) with
    | some entry => .ok entry
    | none => .error s!"unknown check `{name}`; known checks: {(registry.map (·.name)).toList}"

/-- Walk a module's commands, gathering a `FixRecord` per suggested edit.

Each command is elaborated **once** (`elabCommandAtFrontend`) — that advances env/scope for later
commands and populates the info trees the two type-aware rules consult — then detection runs after,
reusing those trees. `#eval`/`#eval!` are never elaborated (they run user code); `initialize` is
skipped in imported mode (already present — re-elaborating an imported decl panics). `commitInit`
(growing-env mode) also commits `initialize`, since declarations there are not pre-imported. -/
partial def collectLoop (all commitInit : Bool) (checks : Array RuleEntry) (acc : Array FixRecord) :
    FrontendM (Array FixRecord) := do
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
    let found ← runCommandElabM (collectFixRecords all checks cmd)
    pure (acc ++ found)
  if isTerminalCommand cmd then return acc else collectLoop all commitInit checks acc

/-- Run `f` over `xs` with at most `conc` concurrent tasks (`conc = 1` ⇒ sequential), preserving
input order. `f` handles its own errors. -/
private partial def drainSharedQueue {α β : Type} (xs : Array α) (f : α → IO β) (nextIndex : IO.Ref Nat)
    (results : IO.Ref (Array (Option β))) : IO Unit := do
  let index ← nextIndex.modifyGet fun index => (index, index + 1)
  let some x := xs[index]? | return
  try
    let result ← f x
    results.modify (·.set! index (some result))
  catch _ => pure ()
  drainSharedQueue xs f nextIndex results

def parMap {α β : Type} (conc : Nat) (xs : Array α) (f : α → IO β) : IO (Array β) := do
  let nextIndex ← IO.mkRef 0
  let results ← IO.mkRef (Array.replicate xs.size none)
  let workers ← (Array.range (min (max 1 conc) xs.size)).mapM fun _ =>
    IO.asTask (drainSharedQueue xs f nextIndex results)
  for worker in workers do
    let _ ← IO.wait worker
  return (← results.get).filterMap id

end FixReporting
