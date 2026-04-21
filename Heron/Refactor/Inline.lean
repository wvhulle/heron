module

public meta import Heron.Refactor
public meta import Lean.Meta.Tactic.Delta
public meta import Lean.Meta.RecExt
public meta import Lean.PrettyPrinter

public section

open Lean Elab Command Meta Heron

/-- Check if an expression references its own name (recursive). -/
meta def isRecursive (value : Expr) (name : Name) : Bool :=
  value.find? (fun e => e.isConst && e.constName? == some name) |>.isSome

/-- Like `delta?` but also expands opaque definitions (e.g. `meta def`). -/
meta def expandConst? (e : Expr) : CoreM (Option Expr) :=
  matchConst e.getAppFn (fun _ => return none) fun fInfo fLvls => do
    if fInfo.hasValue (allowOpaque := true) && fInfo.levelParams.length == fLvls.length then
      let f ← instantiateValueLevelParams fInfo fLvls
      return some (f.betaRev e.getAppRevArgs (useZeta := true))
    else
      return none

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
      -- Well-founded / structural recursion compiles away the self-reference
      -- into `brecOn`/`rec` calls, so `isRecursive` alone is not enough.
      !Meta.recExt.isTagged env name &&
      match env.find? name >>= (·.value? (allowOpaque := true)) with
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
    if let some expanded ← runInfoMetaM ci ti.lctx (expandConst? ti.expr) then
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

private meta instance : Refactor InlineMatch where
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

@[code_action_provider]
public meta def inlineProvider := Refactor.toCodeActionProvider (α := InlineMatch)

meta initialize Refactor.register (α := InlineMatch)
