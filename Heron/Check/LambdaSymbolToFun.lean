module

public meta import Heron.Check
meta import Heron.Register

set_option linter.syntaxKindOrAtomInspection false
set_option linter.syntheticSyntaxConstruction false

open Lean Elab Command Parser Heron

private structure LambdaSymbolToFunMatch where
  lambdaKeyword : Syntax

private meta def lambdaKeyword? (stx : Syntax) : Option Syntax := do
  let keyword ← stx.getHead?
  guard (keyword.getAtomVal == "λ")
  return keyword

private meta instance : Check LambdaSymbolToFunMatch where
  name := `lambdaSymbolToFun
  description := "Suggests `fun` instead of `λ`."
  kinds := #[``Term.fun]
  severity := .information
  category := .style
  detect := fun stx => pure <| (lambdaKeyword? stx).toArray.map ({ lambdaKeyword := · })
  message := fun _ => m!"Write `fun` instead of `λ`"
  emphasize := fun m => m.lambdaKeyword
  sources := #[
    .functionalProgrammingInLean "Anonymous functions" "Getting-to-Know-Lean/Additional-Conveniences/#anonymous-functions",
    .leanStdStyleGuide "Notation and Unicode" "notation-and-unicode",
    .mathlibStyleGuide "Anonymous functions" "anonymous-functions"]
  explanation := fun _ =>
    m!"Lean accepts `λ` as a synonym for `fun`, but `fun` is what most Lean code and the official \
       books use, and it is easier to type."
  replacements := some fun m => return #[{
    emphasizedSyntax := m.lambdaKeyword
    oldSyntax := m.lambdaKeyword
    newSyntax := mkAtom "fun"
    inlineViolationLabel := m!"λ → fun"
  }]

register_check LambdaSymbolToFunMatch
