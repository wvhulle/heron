module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure LambdaSymbolToFunMatch where
  lambdaKeyword : Syntax

private meta def lambdaKeyword? (stx : Syntax) : Option Syntax := do
  let keyword ← stx.getHead?
  guard (keyword.getAtomVal == "λ")
  return keyword

private meta instance : Check LambdaSymbolToFunMatch where
  name := `lambdaSymbolToFun
  kinds := #[``Term.fun]
  severity := .information
  category := .style
  detect := fun stx => pure <| (lambdaKeyword? stx).toArray.map ({ lambdaKeyword := · })
  message := fun _ => m!"Write `fun` instead of `λ`"
  emphasize := fun m => m.lambdaKeyword
  reference := some
    { topic := "Anonymous functions"
      url := "https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#anonymous-functions" }
  explanation := fun _ =>
    m!"Lean accepts `λ` as a synonym for `fun`, but `fun` is what most Lean code and the official \
       books use, and it is easier to type."
  replacements := fun m => return #[{
    emphasizedSyntax := m.lambdaKeyword
    oldSyntax := m.lambdaKeyword
    newSyntax := mkAtom "fun"
    inlineViolationLabel := m!"λ → fun"
  }]

meta initialize Check.register (α := LambdaSymbolToFunMatch)
