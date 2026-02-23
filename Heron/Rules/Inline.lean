import Heron.Rules.Basic
import Lean.Meta.Tactic.Delta
import Lean.PrettyPrinter

open Lean Elab Command Meta Heron.Rules

private structure InlineFixData where
  stx : Syntax
  newText : String

private def detectInlineOpportunities (stx : Syntax) : CommandElabM (Array InlineFixData) := do
  let trees ← collectElabInfoTrees stx
  let env ← getEnv
  let infos := trees.flatMap collectTermInfos
  let mut fixes : Array InlineFixData := #[]
  -- Inline const applications
  let constUsages := infos.filter fun (_, ti) =>
    ti.expr.getAppFn.isConst &&
    match ti.expr.getAppFn.constName? with
    | some name =>
      !env.isProjectionFn name &&
      !Meta.isInstanceCore env name &&
      match env.find? name with
      | some cinfo => match cinfo.value? with
        | some value => !isRecursive value name
        | none => false
      | none => false
    | none => false
  let deduped := deduplicateByPosition constUsages
  for (ci, ti) in deduped do
    try
      let result ← runInfoMetaM ci ti.lctx (delta? ti.expr)
      if let some expanded := result then
        let newText ← runInfoMetaM ci ti.lctx do
          return s!"({← ppExpr expanded})"
        fixes := fixes.push { stx := ti.stx, newText }
    catch _ => pure ()
  -- Inline let-bindings
  let letCandidates := infos.filter fun (_, ti) => ti.expr.isLet
  for (ci, ti) in letCandidates do
    if let .letE _ _ value body _ := ti.expr then
      try
        let newText ← runInfoMetaM ci ti.lctx do
          return s!"({← ppExpr (body.instantiate1 value)})"
        fixes := fixes.push { stx := ti.stx, newText }
      catch _ => pure ()
  return fixes

instance : Rule InlineFixData where
  name := `inline
  detect := detectInlineOpportunities
  diagStx := (·.stx)
  hintMsg := m!"Can be inlined."
  diagMsg := m!"Inline."
  toSuggestion := fun d => { suggestion := d.newText, span? := some d.stx }

initialize Rule.initOption (α := InlineFixData)
initialize Rule.addLinter (α := InlineFixData)

namespace Tests

#eval Rule.addLinter (α := InlineFixData)

def double (n : Nat) := n + n

#assertEdits inline `(term| double 3) => `(term| (3 + 3)) in
example : Nat := double 3

def myConst := 42

def d := double myConst

#assertEdits inline `(term| myConst) => `(term| (42)) in
example : Nat := myConst

end Tests
