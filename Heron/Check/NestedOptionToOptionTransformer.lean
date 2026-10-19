module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Meta Parser Heron

private structure NestedOptionToOptionTransformerMatch where
  stx : Syntax
  /-- The outer monad applied to its leading args, e.g. `(StateT σ m)` or just `m`. -/
  outerMonad : Term
  /-- The `Option`'s value-type args (`α α₁ … αₙ`). -/
  valueArgs : TSyntaxArray `term
  rewriteElaborates : Bool := false

private meta def detectCandidate? :
    Syntax → CommandElabM (Option NestedOptionToOptionTransformerMatch)
  | stx@`($outerFn:ident $outerLeading* (Option $α $αs*)) => do
    let outerMonad ← if outerLeading.isEmpty then pure (outerFn : Term)
      else `(($outerFn $outerLeading*))
    return some { stx, outerMonad, valueArgs := #[α] ++ αs }
  | _ => return none

set_option hygiene false in
private meta def optionTType (m : NestedOptionToOptionTransformerMatch) : CommandElabM Term :=
  `(OptionT $(#[m.outerMonad] ++ m.valueArgs)*)

private meta def wrapsOptionInAnotherMonad (e : Expr) : MetaM Bool := do
  if e.getAppFn.isConstOf ``Option then return false
  outerHasMonadInstance e

private meta def detectInSignature (node : Syntax) :
    CommandElabM (Array NestedOptionToOptionTransformerMatch) := do
  let some m ← detectCandidate? node | return #[]
  let some true ← runMetaMForSyntax m.stx wrapsOptionInAnotherMonad | return #[]
  return #[{ m with rewriteElaborates := ← rewriteElaborates m.stx (← optionTType m) }]

private meta instance : Check NestedOptionToOptionTransformerMatch where
  name := `nestedOptionToOptionTransformer
  description := "Suggests `OptionT` instead of nesting `Option` inside another monad in a signature; the fix is only offered when the rewritten definition still elaborates."
  kinds := #[``Term.app]
  within := #[``Command.declSig, ``Command.optDeclSig]
  severity := .information
  category := .style
  detect := detectInSignature
  message := fun _ => m!"Consider using `OptionT` instead of nesting `Option`"
  emphasize := fun m => m.stx
  sources := #[.functionalProgrammingInLean "Monad transformers"
    "Monad-Transformers/A-Monad-Construction-Kit/#OptionT"]
  explanation := fun m =>
    m!"`OptionT m α` is defined as `m (Option α)`, so this signature already is the transformer \
       type. Writing it as `OptionT` lets `do`-notation handle the failure case: `failure` \
       short-circuits and a `let x ← act` binds the `α`, instead of matching on `some`/`none` \
       after every action.{if m.rewriteElaborates then "" else " The body does not elaborate \
       unchanged with the transformer type (it builds `Option` values by hand), so no automatic \
       fix is offered."} Callers in other declarations may need `.run` to get the nested type back."
  replacements := some fun m => do
    unless m.rewriteElaborates do return #[]
    return #[{ emphasizedSyntax := m.stx
               oldSyntax := m.stx
               newSyntax := ← optionTType m
               inlineViolationLabel := m!"Option → OptionT" }]

register_check NestedOptionToOptionTransformerMatch
