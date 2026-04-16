module

public meta import Heron.Refactor
public meta import Lean.Meta.Tactic.Delta
public meta import Lean.PrettyPrinter

public section

open Lean Elab Command Meta Heron

/-- Check if an expression references its own name (recursive). -/
meta def isRecursive (value : Expr) (name : Name) : Bool :=
  value.find? (fun e => e.isConst && e.constName? == some name) |>.isSome

private inductive InlineKind where
  | const (name : Name)
  | letBinding

private structure InlineMatch where
  stx : Syntax
  newSyntax : Syntax
  kind : InlineKind

meta def isInlineableUsage (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some name =>
    !env.isProjectionFn name && !Meta.isInstanceCore env name &&
      match env.find? name >>= (·.value?) with
      | some v => !isRecursive v name
      | none => false
  | none => false

private meta def detectInlineOpportunities (stx : Syntax) : CommandElabM (Array InlineMatch) := do
  let trees ← collectInfoTrees stx
  let env ← getEnv
  let infos := trees.flatMap collectTermInfos
  let declRange? := getDeclIdRange? stx
  let mut results : Array InlineMatch := #[]
  let constCandidates := infos.filter fun (_, ti) => outsideDeclId declRange? ti && isInlineableUsage env ti.expr
  for (ci, ti) in deduplicateTermInfos constCandidates do
    if let some expanded ← runInfoMetaM ci ti.lctx (delta? ti.expr) then
      try
        let delabbed ← runInfoMetaM ci ti.lctx (PrettyPrinter.delab expanded)
        let name := ti.expr.getAppFn.constName?.getD `unknown
        let parensed ← `(($delabbed))
        results := results.push { stx := ti.stx, newSyntax := parensed, kind := .const name }
      catch _ => pure ()
  for (ci, ti) in infos do
    if let .letE _ _ value body _ := ti.expr then
      try
        let delabbed ← runInfoMetaM ci ti.lctx (PrettyPrinter.delab (body.instantiate1 value))
        let parensed ← `(($delabbed))
        results := results.push { stx := ti.stx, newSyntax := parensed, kind := .letBinding }
      catch _ => pure ()
  return results

private meta def inlineLabel : InlineKind → MessageData
  | .const name => m!"Inline '{name}'"
  | .letBinding => m!"Inline let binding"

@[refactor_rule] private meta instance : Refactor InlineMatch where
  name := `inline
  detect := detectInlineOpportunities
  message := fun m => inlineLabel m.kind
  replacements := fun m => return #[{
    emphasizedSyntax := m.stx
    oldSyntax := m.stx
    newSyntax := m.newSyntax
    inlineViolationLabel := inlineLabel m.kind
  }]
  codeActionKind := "refactor.inline"
