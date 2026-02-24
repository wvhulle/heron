import Heron.Rules.Basic
import Lean.Meta.Tactic.Delta

open Lean Elab Command Meta Heron.Rules

private structure InlineFixData where
  stx : Syntax
  newText : String

private def isInlineableUsage (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some name =>
    !env.isProjectionFn name &&
    !Meta.isInstanceCore env name &&
    match env.find? name >>= (·.value?) with
    | some v => !isRecursive v name
    | none => false
  | none => false

private def detectInlineOpportunities (stx : Syntax) : CommandElabM (Array InlineFixData) := do
  let trees ← collectElabInfoTrees stx
  let env ← getEnv
  let infos := trees.flatMap collectTermInfos
  let declRange? := getDeclIdRange? stx
  let mut fixes : Array InlineFixData := #[]
  let constCandidates := infos.filter fun (_, ti) =>
    outsideDeclId declRange? ti && isInlineableUsage env ti.expr
  for (ci, ti) in deduplicateByPosition constCandidates do
    if let some expanded ← runInfoMetaM ci ti.lctx (delta? ti.expr) then
      if let some text ← ppExprFix? ci ti.lctx expanded then
        fixes := fixes.push { stx := ti.stx, newText := text }
  for (ci, ti) in infos do
    if let .letE _ _ value body _ := ti.expr then
      if let some text ← ppExprFix? ci ti.lctx (body.instantiate1 value) then
        fixes := fixes.push { stx := ti.stx, newText := text }
  return fixes

instance : Rule InlineFixData where
  ruleName := `inline
  severity := .warning
  detect := detectInlineOpportunities
  diagnosticNode := (·.stx)
  hintMessage := m!"Can be inlined."
  diagnosticMessage := m!"Inline."
  replacementText := (·.newText)
  replacementNode := (·.stx)

initialize Rule.initOption (α := InlineFixData)
initialize Rule.addLinter (α := InlineFixData)

namespace Tests

#eval Rule.addLinter (α := InlineFixData)

def double (n : Nat) := n + n

#assertEdits inline `(term| double 3) => `(term| (3 + 3)) in
example : Nat := double 3

def myConst := 42

-- The definition site of `d` should not flag `d` itself for inlining.
#assertNoSuggests inline in
def d := 0

#assertEdits inline `(term| myConst) => `(term| (42)) in
example : Nat := myConst

end Tests
