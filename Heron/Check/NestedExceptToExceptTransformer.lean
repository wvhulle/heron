module

public meta import Heron.Check
public meta import Heron.Monad

open Lean Elab Command Meta Parser Heron

private structure NestedExceptToExceptTransformerMatch where
  stx : TSyntax `term
  /-- The outer monad applied to its leading args, e.g. `(StateT σ m)` or just `m`. -/
  outerMonad : TSyntax `term
  /-- The error type `ε` from `Except ε α …`. -/
  errorType : TSyntax `term
  /-- The `Except`'s value-type args (`α α₁ … αₙ`). -/
  valueArgs : TSyntaxArray `term

private meta def detectCandidate? :
    Syntax → CommandElabM (Option NestedExceptToExceptTransformerMatch)
  | stx@`($outerFn:ident $outerLeading* (Except $ε $α $αs*)) => do
    -- Same-constructor nesting belongs to NestedMonadJoin, not this rule.
    if outerFn.getId == `Except then return none
    let outerMonad ← if outerLeading.isEmpty
      then pure (⟨outerFn⟩ : TSyntax `term)
      else `(($outerFn $outerLeading*))
    return some { stx := ⟨stx⟩, outerMonad, errorType := ε, valueArgs := #[α] ++ αs }
  | _ => return none

private meta def exceptTType (m : NestedExceptToExceptTransformerMatch) : CommandElabM (TSyntax `term) :=
  `($(mkIdent `ExceptT) $(#[m.errorType, m.outerMonad] ++ m.valueArgs)*)

private meta def detectInSignature (cmd : Syntax) (node : Syntax) :
    CommandElabM (Option NestedExceptToExceptTransformerMatch) := do
  let some m ← detectCandidate? node | return none
  let some true ← runMetaMForSyntax m.stx outerHasMonadInstance | return none
  let probe := replaceSourceNode cmd m.stx (← exceptTType m)
  unless ← elaboratesWithoutErrorsInProbeNamespace probe do return none
  return some m

private meta instance : Check NestedExceptToExceptTransformerMatch where
  name := `nestedExceptToExceptTransformer
  kinds := #[]
  severity := .information
  category := .style
  detect := fun cmd => (signatureNodes cmd).filterMapM (detectInSignature cmd)
  message := fun _ => m!"Consider using `ExceptT` instead of nesting `Except`"
  emphasize := fun m => m.stx
  reference := some
    { topic := "Monad transformers"
      url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/transformers.html" }
  explanation := fun _ =>
    m!"This nested monad type in the signature is definitionally equal to its `ExceptT` form, \
       and the declaration still elaborates with the `ExceptT` signature. Using the transformer \
       enables do-notation with automatic effect handling. Callers in other declarations may \
       need `.run` to get the nested type back."
  replacements := fun m => do
    return #[{ emphasizedSyntax := m.stx
               oldSyntax := m.stx
               newSyntax := ← exceptTType m
               inlineViolationLabel := m!"Except → ExceptT" }]

meta initialize Check.register (α := NestedExceptToExceptTransformerMatch)
