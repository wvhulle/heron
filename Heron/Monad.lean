module

public meta import Lean.Elab.Command
public meta import Lean.Meta.SynthInstance

public section

open Lean Elab Command Meta

namespace Heron

/-- Extract the `doElem` body of a `doSeqItem` (which wraps a doElem with an
optional trailing `;`). -/
private meta def doSeqItemElem? :
    TSyntax ``Parser.Term.doSeqItem → Option (TSyntax `doElem)
  | `(Parser.Term.doSeqItem| $e:doElem)   => some e
  | `(Parser.Term.doSeqItem| $e:doElem; ) => some e
  | _ => none

/-- Extract the doElem array from a `doSeqIndent` or `doSeqBracketed` node. -/
meta def getDoElems (doSeq : Syntax) : Array (TSyntax `doElem) :=
  let items : Array (TSyntax ``Parser.Term.doSeqItem) :=
    match doSeq with
    | `(Parser.Term.doSeqIndent| $items:doSeqItem*) => items
    | `(Parser.Term.doSeqBracketed| { $items:doSeqItem* }) => items
    | _ => #[]
  items.filterMap doSeqItemElem?

/-- Check if the outer part of a fully-applied expression — everything except
the last argument — has a `Monad` instance. Used by transformer-detection rules
to confirm `f a₁ … aₙ (Wrapped α)` has `f a₁ … aₙ` actually being a monad. -/
meta def outerHasMonadInstance (e : Expr) : MetaM Bool := do
  let args := e.getAppArgs
  if args.size == 0 then return false
  let outerMonad := mkAppN e.getAppFn args.pop
  try
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let monadType := mkAppN (mkConst ``Monad [u, v]) #[outerMonad]
    return (← synthInstance? monadType).isSome
  catch _ => return false

end Heron
