module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure NegatedIfToUnlessMatch where
  ifStx : Syntax
  ifKeyword : Syntax
  thenKeyword : Syntax
  negation : Syntax
  withoutNegation : Syntax

private meta def negationAndRemainder? : Term → Option (Syntax × Syntax)
  | `(!%$bang $_) => some (bang, Syntax.missing)
  | negated@`(not $inner) => some (negated, inner)
  | negated@`(Not $inner) => some (negated, inner)
  | _ => none

private meta def detectNegatedIf (stx : Syntax) : CommandElabM (Array NegatedIfToUnlessMatch) := do
  let `(doElem| if%$ifKeyword $cond:term then%$thenKeyword $_) := stx | return #[]
  let some (negation, withoutNegation) := negationAndRemainder? cond | return #[]
  return #[{ ifStx := stx, ifKeyword, thenKeyword, negation, withoutNegation }]

private meta instance : Check NegatedIfToUnlessMatch where
  name := `negatedIfToUnless
  description := "Suggests `unless` instead of `if not` without an `else` branch."
  kinds := #[``Term.doIf]
  severity := .information
  category := .simplification
  detect := detectNegatedIf
  message := fun _ => m!"Use `unless` instead of `if not`"
  emphasize := fun m => m.ifStx
  sources := #[
    .functionalProgrammingInLean "unless" "Monad-Transformers/More-do-Features/#single-branched-if",
    .hlint "when (not x) ==> unless x"]
  explanation := fun _ => m!"In a do-block, `if not cond then body` can be simplified to `unless cond do body`."
  replacements := some fun m => do
    let `(doElem| unless%$unlessKeyword $_ do%$doKeyword $_) ← `(doElem| unless true do pure ())
      | return #[]
    return #[
    { emphasizedSyntax := m.ifKeyword, oldSyntax := m.ifKeyword, newSyntax := unlessKeyword,
      prettyPrint := printKeyword, inlineViolationLabel := m!"if not → unless" },
    { emphasizedSyntax := m.negation, oldSyntax := m.negation, newSyntax := m.withoutNegation,
      inlineViolationLabel := m!"drop the negation" },
    { emphasizedSyntax := m.thenKeyword, oldSyntax := m.thenKeyword, newSyntax := doKeyword,
      prettyPrint := printKeyword, inlineViolationLabel := m!"then → do" }]

register_check NegatedIfToUnlessMatch
