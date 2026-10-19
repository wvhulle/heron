module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Meta Parser Heron

private structure NestedExceptToExceptTransformerMatch where
  stx : Syntax
  /-- The outer monad applied to its leading args, e.g. `(StateT σ m)` or just `m`. -/
  outerMonad : Term
  /-- The error type `ε` from `Except ε α …`. -/
  errorType : Term
  /-- The `Except`'s value-type args (`α α₁ … αₙ`). -/
  valueArgs : TSyntaxArray `term
  rewriteElaborates : Bool := false

private meta def detectCandidate? :
    Syntax → CommandElabM (Option NestedExceptToExceptTransformerMatch)
  | stx@`($outerFn:ident $outerLeading* (Except $ε $α $αs*)) => do
    let outerMonad ← if outerLeading.isEmpty then pure (outerFn : Term)
      else `(($outerFn $outerLeading*))
    return some { stx, outerMonad, errorType := ε, valueArgs := #[α] ++ αs }
  | _ => return none

set_option hygiene false in
private meta def exceptTType (m : NestedExceptToExceptTransformerMatch) : CommandElabM Term :=
  `(ExceptT $(#[m.errorType, m.outerMonad] ++ m.valueArgs)*)

private meta def wrapsExceptInAnotherMonad (e : Expr) : MetaM Bool := do
  if e.getAppFn.isConstOf ``Except then return false
  outerHasMonadInstance e

private meta def detectInSignature (node : Syntax) :
    CommandElabM (Array NestedExceptToExceptTransformerMatch) := do
  let some m ← detectCandidate? node | return #[]
  let some true ← runMetaMForSyntax m.stx wrapsExceptInAnotherMonad | return #[]
  return #[{ m with rewriteElaborates := ← rewriteElaborates m.stx (← exceptTType m) }]

private meta instance : Check NestedExceptToExceptTransformerMatch where
  name := `nestedExceptToExceptTransformer
  description := "Suggests `ExceptT` instead of nesting `Except` inside another monad in a signature; the fix is only offered when the rewritten definition still elaborates."
  kinds := #[``Term.app]
  within := #[``Command.declSig, ``Command.optDeclSig]
  severity := .information
  category := .style
  detect := detectInSignature
  message := fun _ => m!"Consider using `ExceptT` instead of nesting `Except`"
  emphasize := fun m => m.stx
  sources := #[.functionalProgrammingInLean "Monad transformers"
    "Monad-Transformers/A-Monad-Construction-Kit/#exceptions"]
  explanation := fun m =>
    m!"`ExceptT ε m α` is defined as `m (Except ε α)`, so this signature already is the \
       transformer type. Writing it as `ExceptT` lets `do`-notation handle the error case: \
       `throw` short-circuits and a `let x ← act` binds the `α`, instead of matching on \
       `.ok`/`.error` after every action.{if m.rewriteElaborates then "" else " The body does \
       not elaborate unchanged with the transformer type (it builds `Except` values by hand), so \
       no automatic fix is offered."} Callers in other declarations may need `.run` to get the \
       nested type back."
  replacements := some fun m => do
    unless m.rewriteElaborates do return #[]
    return #[{ emphasizedSyntax := m.stx
               oldSyntax := m.stx
               newSyntax := ← exceptTType m
               inlineViolationLabel := m!"Except → ExceptT" }]

register_check NestedExceptToExceptTransformerMatch
