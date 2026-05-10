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

private meta def detectAtNode (stx : Syntax) :
    CommandElabM (Array OptionToOptionTMatch) := do
  let some m ← detectCandidate? stx | return #[]
  let some hasMonad ← runMetaMForSyntax m.stx outerHasMonadInstance | return #[]
  return if hasMonad then #[m] else #[]

private meta instance : Check OptionToOptionTMatch where
  name := `optionToOptionT
  kinds := #[``Term.app]
  severity := .information
  category := .style
  detect := detectAtNode
  message := fun _ => m!"Consider using `OptionT` instead of nesting `Option`"
  emphasize := fun m => m.stx
  reference := some
    { topic := "Monad transformers"
      url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/transformers.html" }
  explanation := fun _ =>
    m!"This nested monad type is definitionally equal to its `OptionT` form. \
       Using the transformer alias enables do-notation with automatic effect handling."
  replacements := fun m => do
    let optT := mkIdent `OptionT
    let allArgs := #[m.outerMonad] ++ m.valueArgs
    let repl ← `($optT $allArgs*)
    return #[{ emphasizedSyntax := m.stx
               oldSyntax := m.stx
               newSyntax := repl
               inlineViolationLabel := m!"Option → OptionT" }]

meta initialize Check.register (α := OptionToOptionTMatch)
