import Heron.Provider.Refactor
import Heron.AssertEdits
import Heron.AssertNoSuggests
import Lean.Meta.Tactic.Delta
import Lean.PrettyPrinter

open Lean Elab Command Meta Heron.Provider

/-- Check if an expression references its own name (recursive). -/
private def isRecursive (value : Expr) (name : Name) : Bool :=
  value.find? (fun e => e.isConst && e.constName? == some name) |>.isSome

private inductive InlineKind where
  | const (name : Name)
  | letBinding

private structure InlineFixData where
  stx : Syntax
  newText : String
  kind : InlineKind

private def isInlineableUsage (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some name =>
    !env.isProjectionFn name && !Meta.isInstanceCore env name &&
      match env.find? name >>= (·.value?) with
      | some v => !isRecursive v name
      | none => false
  | none => false

private def detectInlineOpportunities (stx : Syntax) : CommandElabM (Array InlineFixData) := do
  let trees ← collectInfoTrees stx
  let env ← getEnv
  let infos := trees.flatMap collectTermInfos
  let declRange? := getDeclIdRange? stx
  let mut fixes : Array InlineFixData := #[]
  let constCandidates := infos.filter fun (_, ti) => outsideDeclId declRange? ti && isInlineableUsage env ti.expr
  for (ci, ti) in deduplicateTermInfos constCandidates do
    if let some expanded ← runInfoMetaM ci ti.lctx (delta? ti.expr) then
      if let some text ← ppExprFix? ci ti.lctx expanded then
        let name := ti.expr.getAppFn.constName?.getD `unknown
        fixes := fixes.push { stx := ti.stx, newText := text, kind := .const name }
  for (ci, ti) in infos do
    if let .letE _ _ value body _ := ti.expr then
      if let some text ← ppExprFix? ci ti.lctx (body.instantiate1 value) then
        fixes := fixes.push { stx := ti.stx, newText := text, kind := .letBinding }
  return fixes

private def inlineLabel : InlineKind → MessageData
  | .const name => m!"Inline '{name}'"
  | .letBinding => m!"Inline let binding"

@[refactor_rule] instance : Refactor InlineFixData where
  ruleName := `inline
  detect := detectInlineOpportunities
  hintMessage := fun fd => inlineLabel fd.kind
  replacements := fun fd => #[{
    sourceNode := fd.stx
    replacementNode := fd.stx
    replacementText := fd.newText
    sourceLabel := inlineLabel fd.kind
  }]
  codeActionKind := "refactor.inline"

namespace Tests

def double (n : Nat) :=
  n + n

#assertEdits inline `(term| double 3) => `(term| (3 + 3)) in
example : Nat := double 3

def myConst :=
  42

-- The definition site of `d` should not flag `d` itself for inlining.
#assertNoSuggests inline in
  def d :=
    0

#assertEdits inline `(term| myConst) => `(term| (42)) in
example : Nat := myConst

end Tests
