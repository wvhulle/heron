module

public meta import Heron.Check

open Lean Elab Command Meta Parser Heron

private structure NestedMonadToTransformerMatch where
  stx : TSyntax `term
  transformerName : Name
  /-- The outer monad applied to its leading args, e.g. `(StateT σ m)` or just `m`. -/
  outerMonad : TSyntax `term
  /-- Inner-constructor args appearing *before* the outer monad in the transformer
  call (e.g. `[ε]` for `Except ε α → ExceptT ε m α`; empty for `Option`). -/
  erasureArgs : TSyntaxArray `term
  /-- Inner-constructor args appearing *after* the outer monad. -/
  valueArgs : TSyntaxArray `term

private structure Split where
  innerName : Name
  transformerName : Name
  erasureArgs : TSyntaxArray `term
  valueArgs : TSyntaxArray `term

/-- Recognise the inner constructor and split its argument list according to
where the outer monad must be inserted in the transformer alias. -/
private meta def splitInner? : TSyntax `term → Option Split
  | `(Option $α $αs*) => some
      { innerName := `Option, transformerName := `OptionT
        erasureArgs := #[], valueArgs := #[α] ++ αs }
  | `(Except $ε $α $αs*) => some
      { innerName := `Except, transformerName := `ExceptT
        erasureArgs := #[ε], valueArgs := #[α] ++ αs }
  | _ => none

/-- A syntactic candidate before Monad verification. -/
private structure Candidate extends NestedMonadToTransformerMatch

/-- Detect a candidate at a single node: `f ... (Option α)` or `f ... (Except ε α)`.
Excludes cases where outer and inner constructor match (handled by NestedMonadJoin). -/
private meta def detectCandidate? : Syntax → CommandElabM (Option Candidate)
  | stx@`($outerFn:ident $outerLeading* ($inner:term)) => do
    let some split := splitInner? inner | return none
    if outerFn.getId == split.innerName then return none
    let outerMonad ← if outerLeading.isEmpty
      then pure (⟨outerFn⟩ : TSyntax `term)
      else `(($outerFn $outerLeading*))
    return some { toNestedMonadToTransformerMatch :=
      { stx := ⟨stx⟩
        transformerName := split.transformerName
        outerMonad
        erasureArgs := split.erasureArgs
        valueArgs := split.valueArgs } }
  | _ => pure none

/-- Check if the outer part of an expression (everything except the last arg) has a Monad instance. -/
private meta def outerHasMonadInstance (e : Expr) : MetaM Bool := do
  let args := e.getAppArgs
  if args.size == 0 then
    return false
  let outerMonad := mkAppN e.getAppFn args.pop
  try
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let monadType := mkAppN (mkConst ``Monad [u, v]) #[outerMonad]
    return (← synthInstance? monadType).isSome
  catch _ =>
    return false

private meta def detectAtNode (stx : Syntax) : CommandElabM (Array NestedMonadToTransformerMatch) := do
  let some cand ← detectCandidate? stx | return #[]
  let trees ← collectInfoTrees stx
  let infos := trees.flatMap collectTermInfos
  let deduped := deduplicateTermInfos infos
  let some pos := cand.stx.raw.getPos? true | return #[]
  let entry? := deduped.findSome? fun (ci, ti) =>
    match ti.stx.getPos? true with
    | some p => if p.byteIdx == pos.byteIdx then some (ci, ti) else none
    | none => none
  let some (ci, ti) := entry? | return #[]
  let hasMonad ← runInfoMetaM ci ti.lctx (outerHasMonadInstance ti.expr)
  if hasMonad then return #[cand.toNestedMonadToTransformerMatch] else return #[]

private meta instance : Check NestedMonadToTransformerMatch
    where
  name := `nestedMonadToTransformer
  kinds := #[``Term.app]
  severity := .information
  category := .style
  detect := detectAtNode
  message := fun m => m! "Consider using `{m.transformerName}` instead of nesting"
  emphasize := fun m => m.stx
  tags := #[]
  reference :=
    some
      { topic := "Monad transformers"
        url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/transformers.html" }
  explanation := fun m => m! "This nested monad type is definitionally equal to its `{m.transformerName}` form. \
       Using the transformer alias enables do-notation with automatic effect handling."
  replacements := fun m => do
    let tName := mkIdent m.transformerName
    let allArgs := m.erasureArgs ++ #[m.outerMonad] ++ m.valueArgs
    let repl ← `($tName $allArgs*)
    return #[{ emphasizedSyntax := m.stx
               oldSyntax := m.stx
               newSyntax := repl
               inlineViolationLabel := m!"transformer alias" }]

meta initialize Check.register (α := NestedMonadToTransformerMatch)
