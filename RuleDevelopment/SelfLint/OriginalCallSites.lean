module

public meta import Heron.Rule
meta import Lean.Elab.BuiltinTerm

public section

open Lean Elab Command Meta

namespace Heron

private meta def isApplicationSyntax : Syntax → Bool
  | `($_:term $_*) => true
  | _ => false

private meta def termInfosOutsideNameLiterals (tree : InfoTree) : Array (ContextInfo × TermInfo) :=
  let collect : StateM (Array (ContextInfo × TermInfo)) Unit :=
    tree.visitM' (preNode := fun ci info _ => do
      let .ofTermInfo ti := info | return true
      if ti.elaborator == ``Lean.Elab.Term.elabDoubleQuotedName then return false
      modify (·.push (ci, ti))
      return true)
  (collect.run #[]).2

private meta def originalTermInfosWithin (node : Syntax) (keep : Syntax → Bool) (isTarget : Expr → Bool) :
    CommandElabM (Array Syntax) := do
  let trees ← collectInfoTrees node
  let hits ← (trees.flatMap termInfosOutsideNameLiterals).filterM fun (ci, ti) => do
    let .original .. := ti.stx.getHeadInfo | return false
    unless liesWithin node ti.stx && keep ti.stx do return false
    runInfoMetaM ci ti.lctx do return isTarget (← instantiateMVars ti.expr)
  return (deduplicateTermInfos hits).map (·.2.stx)

meta def originalCallSitesOf (node : Syntax) (isTarget : Expr → Bool) : CommandElabM (Array Syntax) :=
  originalTermInfosWithin node (!isApplicationSyntax ·) isTarget

meta def originalApplicationsOf (node : Syntax) (isTarget : Expr → Bool) : CommandElabM (Array Syntax) :=
  originalTermInfosWithin node isApplicationSyntax isTarget

end Heron
