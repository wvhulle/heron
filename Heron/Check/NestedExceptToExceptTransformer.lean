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
  rewriteElaborates : Bool := false

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
  return some { m with rewriteElaborates := ← elaboratesWithoutErrorsInProbeNamespace probe }

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
      url := "https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/A-Monad-Construction-Kit/#exceptions" }
  explanation := fun m =>
    m!"`ExceptT ε m α` is defined as `m (Except ε α)`, so this signature already is the \
       transformer type. Writing it as `ExceptT` lets `do`-notation handle the error case: \
       `throw` short-circuits and a `let x ← act` binds the `α`, instead of matching on \
       `.ok`/`.error` after every action.{if m.rewriteElaborates then "" else " The body does \
       not elaborate unchanged with the transformer type (it builds `Except` values by hand), so \
       no automatic fix is offered."} Callers in other declarations may need `.run` to get the \
       nested type back."
  replacements := fun m => do
    unless m.rewriteElaborates do return #[]
    return #[{ emphasizedSyntax := m.stx
               oldSyntax := m.stx
               newSyntax := ← exceptTType m
               inlineViolationLabel := m!"Except → ExceptT" }]

meta initialize Check.register (α := NestedExceptToExceptTransformerMatch)
