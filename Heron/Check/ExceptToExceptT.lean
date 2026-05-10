module

public meta import Heron.Check

open Lean Elab Command Meta Parser Heron

private structure ExceptToExceptTMatch where
  stx : TSyntax `term
  /-- The outer monad applied to its leading args, e.g. `(StateT σ m)` or just `m`. -/
  outerMonad : TSyntax `term
  /-- The error type `ε` from `Except ε α …`. -/
  errorType : TSyntax `term
  /-- The `Except`'s value-type args (`α α₁ … αₙ`). -/
  valueArgs : TSyntaxArray `term

private meta def detectCandidate? :
    Syntax → CommandElabM (Option ExceptToExceptTMatch)
  | stx@`($outerFn:ident $outerLeading* (Except $ε $α $αs*)) => do
    -- Same-constructor nesting belongs to NestedMonadJoin, not this rule.
    if outerFn.getId == `Except then return none
    let outerMonad ← if outerLeading.isEmpty
      then pure (⟨outerFn⟩ : TSyntax `term)
      else `(($outerFn $outerLeading*))
    return some { stx := ⟨stx⟩, outerMonad, errorType := ε, valueArgs := #[α] ++ αs }
  | _ => return none

private meta def detectAtNode (stx : Syntax) :
    CommandElabM (Array ExceptToExceptTMatch) := do
  let some m ← detectCandidate? stx | return #[]
  let some hasMonad ← runMetaMForSyntax m.stx outerHasMonadInstance | return #[]
  return if hasMonad then #[m] else #[]

private meta instance : Check ExceptToExceptTMatch where
  name := `exceptToExceptT
  kinds := #[``Term.app]
  severity := .information
  category := .style
  detect := detectAtNode
  message := fun _ => m!"Consider using `ExceptT` instead of nesting `Except`"
  emphasize := fun m => m.stx
  reference := some
    { topic := "Monad transformers"
      url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/transformers.html" }
  explanation := fun _ =>
    m!"This nested monad type is definitionally equal to its `ExceptT` form. \
       Using the transformer alias enables do-notation with automatic effect handling."
  replacements := fun m => do
    let exceptT := mkIdent `ExceptT
    let allArgs := #[m.errorType, m.outerMonad] ++ m.valueArgs
    let repl ← `($exceptT $allArgs*)
    return #[{ emphasizedSyntax := m.stx
               oldSyntax := m.stx
               newSyntax := repl
               inlineViolationLabel := m!"Except → ExceptT" }]

meta initialize Check.register (α := ExceptToExceptTMatch)
