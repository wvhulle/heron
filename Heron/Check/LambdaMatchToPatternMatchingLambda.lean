module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure LambdaMatchToPatternMatchingLambdaMatch where
  funStx : Syntax
  matchAlts : Syntax

private meta def mentionsName (name : Name) (stx : Syntax) : Bool :=
  (stx.find? fun s => s.isIdent && (s.getId == name || s.getId.getRoot == name)).isSome

private meta instance : Check LambdaMatchToPatternMatchingLambdaMatch where
  name := `lambdaMatchToPatternMatchingLambda
  description := "Suggests `fun | …` instead of a lambda whose body only matches on its argument."
  kinds := #[``Term.fun]
  severity := .information
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | `(fun $x:ident => match $discr:ident with $alts:matchAlts) =>
      if discr.getId == x.getId && !mentionsName x.getId alts then #[{ funStx := stx, matchAlts := alts }]
      else #[]
    | _ => #[]
  message := fun _ => m!"Use `fun | ...` pattern matching syntax"
  emphasize := fun m => m.funStx
  sources := #[.functionalProgrammingInLean "Anonymous functions"
    "Getting-to-Know-Lean/Additional-Conveniences/#anonymous-functions"]
  explanation := fun _ =>
    m!"`fun x => match x with | ...` can be simplified to `fun | ...` using Lean's pattern-matching lambda syntax, because no match arm refers to `x` itself."
  replacements := some fun m => do
    let alts : TSyntax ``Term.matchAlts := ⟨m.matchAlts⟩
    let repl ← `(fun$alts:matchAlts)
    return #[{
          emphasizedSyntax := m.funStx
          oldSyntax := m.funStx
          newSyntax := repl
          inlineViolationLabel := m!"fun match → fun |" }]

register_check LambdaMatchToPatternMatchingLambdaMatch
