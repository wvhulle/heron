module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure FunMatchToMatchFunMatch where
  funStx : Syntax
  matchAlts : Syntax

private meta instance : Check FunMatchToMatchFunMatch where
  name := `funMatchToMatchFun
  kinds := #[``Term.fun]
  severity := .information
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | `(fun $x:ident => match $discr:ident with $alts:matchAlts) =>
      if discr.getId == x.getId then #[{ funStx := stx, matchAlts := alts }]
      else #[]
    | _ => #[]
  message := fun _ => m!"Use `fun | ...` pattern matching syntax"
  emphasize := fun m => m.funStx
  reference :=
    some
      { topic := "Anonymous functions",
        url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ =>
    m!"`fun x => match x with | ...` can be simplified to `fun | ...` using Lean's pattern matching lambda syntax."
  replacements := fun m => do
    let alts : TSyntax ``Term.matchAlts := ⟨m.matchAlts⟩
    let repl ← `(fun$alts:matchAlts)
    return #[{
          emphasizedSyntax := m.funStx
          oldSyntax := m.funStx
          newSyntax := repl
          inlineViolationLabel := m!"fun match → fun |" }]

meta initialize Check.register (α := FunMatchToMatchFunMatch)
