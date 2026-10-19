module

public meta import Lean.Elab.Command
public meta import Lean.Meta.SynthInstance
public meta import Heron.Rule

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

meta def doBlockOf [Monad m] [MonadQuotation m] (elems : Array (TSyntax `doElem)) : m Term := do
  let items ← elems.mapM fun elem => `(Parser.Term.doSeqItem| $elem:doElem)
  let seq : TSyntax ``Parser.Term.doSeq := ⟨← `(Parser.Term.doSeqIndent| $items:doSeqItem*)⟩
  `(do $seq)

meta partial def subtreeNodes (stx : Syntax) : Array Syntax :=
  #[stx] ++ stx.getArgs.flatMap subtreeNodes

meta partial def signatureNodes (cmd : Syntax) : Array Syntax :=
  match cmd with
  | .node _ kind args =>
    if kind == ``Parser.Command.declSig || kind == ``Parser.Command.optDeclSig then subtreeNodes cmd
    else args.flatMap signatureNodes
  | _ => #[]

private meta def isSameSourceNode (candidate target : Syntax) : Bool :=
  candidate.getKind == target.getKind &&
    candidate.getPos? == target.getPos? && candidate.getTailPos? == target.getTailPos?

meta def replaceSourceNode (cmd target replacement : Syntax) : Syntax :=
  Id.run <| cmd.replaceM fun node =>
    pure (if isSameSourceNode node target then some replacement else none)

meta def _root_.Lean.TSyntax.replacingSourceNode (stx : TSyntax k) (target replacement : Syntax) :
    TSyntax k :=
  ⟨replaceSourceNode stx target replacement⟩

private meta def spans (outer inner : Syntax.Range) : Bool :=
  outer.start ≤ inner.start && inner.stop ≤ outer.stop

meta def enclosingCommand? (node : Syntax) : CommandElabM (Option Syntax) := do
  let some range := node.getRange? | return none
  let commands := (← getInfoState).trees.toArray.flatMap fun tree =>
    tree.foldInfo (init := #[]) fun _ info acc =>
      match info with
      | .ofCommandInfo ci => if ci.stx.getRange?.any (spans · range) then acc.push ci.stx else acc
      | _ => acc
  return commands.foldl (init := none) fun outermost? candidate =>
    match outermost?.bind (·.getRange?), candidate.getRange? with
    | some current, some next => if spans next current then some candidate else outermost?
    | _, _ => some candidate

meta def rewriteElaborates (target replacement : Syntax) : CommandElabM Bool := do
  let some cmd ← enclosingCommand? target | return false
  elaboratesWithoutErrorsInProbeNamespace (replaceSourceNode cmd target replacement)

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
