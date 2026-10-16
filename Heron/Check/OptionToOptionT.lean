module

public meta import Heron.Check
public meta import Heron.Monad

open Lean Elab Command Meta Parser Heron

private structure OptionToOptionTMatch where
  stx : TSyntax `term
  /-- The outer monad applied to its leading args, e.g. `(StateT σ m)` or just `m`. -/
  outerMonad : TSyntax `term
  /-- The `Option`'s value-type args (`α α₁ … αₙ`). -/
  valueArgs : TSyntaxArray `term

private meta def detectCandidate? :
    Syntax → CommandElabM (Option OptionToOptionTMatch)
  | stx@`($outerFn:ident $outerLeading* (Option $α $αs*)) => do
    -- Same-constructor nesting belongs to NestedMonadJoin, not this rule.
    if outerFn.getId == `Option then return none
    let outerMonad ← if outerLeading.isEmpty
      then pure (⟨outerFn⟩ : TSyntax `term)
      else `(($outerFn $outerLeading*))
    return some { stx := ⟨stx⟩, outerMonad, valueArgs := #[α] ++ αs }
  | _ => return none

private meta def optionTType (m : OptionToOptionTMatch) : CommandElabM (TSyntax `term) :=
  `($(mkIdent `OptionT) $(#[m.outerMonad] ++ m.valueArgs)*)

private meta def detectInSignature (cmd : Syntax) (node : Syntax) :
    CommandElabM (Option OptionToOptionTMatch) := do
  let some m ← detectCandidate? node | return none
  let some true ← runMetaMForSyntax m.stx outerHasMonadInstance | return none
  let probe := replaceSourceNode cmd m.stx (← optionTType m)
  unless ← elaboratesWithoutErrorsInProbeNamespace probe do return none
  return some m

private meta instance : Check OptionToOptionTMatch where
  name := `optionToOptionT
  kinds := #[]
  severity := .information
  category := .style
  detect := fun cmd => (signatureNodes cmd).filterMapM (detectInSignature cmd)
  message := fun _ => m!"Consider using `OptionT` instead of nesting `Option`"
  emphasize := fun m => m.stx
  reference := some
    { topic := "Monad transformers"
      url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/transformers.html" }
  explanation := fun _ =>
    m!"This nested monad type in the signature is definitionally equal to its `OptionT` form, \
       and the declaration still elaborates with the `OptionT` signature. Using the transformer \
       enables do-notation with automatic effect handling. Callers in other declarations may \
       need `.run` to get the nested type back."
  replacements := fun m => do
    return #[{ emphasizedSyntax := m.stx
               oldSyntax := m.stx
               newSyntax := ← optionTType m
               inlineViolationLabel := m!"Option → OptionT" }]

meta initialize Check.register (α := OptionToOptionTMatch)
