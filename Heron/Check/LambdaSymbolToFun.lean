module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure LambdaSymbolToFunMatch where
  funStx : Syntax
  lambdaKeyword : Syntax
  funKeyword : Syntax

private meta def keywordOf : Syntax → Option Syntax
  | `(fun%$keyword $_* => $_) => some keyword
  | `(fun%$keyword $_:matchAlt*) => some keyword
  | _ => none

private meta def detectLambdaKeyword (stx : Syntax) : CommandElabM (Array LambdaSymbolToFunMatch) := do
  let some keyword := keywordOf stx | return #[]
  let some funKeyword := keywordOf (← `(fun x => x)) | return #[]
  if keyword.structEq funKeyword then return #[]
  return #[{ funStx := stx, lambdaKeyword := keyword, funKeyword }]

private meta instance : Check LambdaSymbolToFunMatch where
  name := `lambdaSymbolToFun
  description := "Suggests `fun` instead of `λ`."
  kinds := #[``Term.fun]
  severity := .information
  category := .style
  detect := detectLambdaKeyword
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
    oldSyntax := m.funStx
    newSyntax := replaceSourceNode m.funStx m.lambdaKeyword m.funKeyword
    inlineViolationLabel := m!"λ → fun" }]

register_check LambdaSymbolToFunMatch
