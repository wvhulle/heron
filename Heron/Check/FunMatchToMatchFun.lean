module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure FunMatchToMatchFunMatch where
  funStx : Syntax
  matchAlts : Syntax

/-- Detect `fun x => match x with | ...` where x is the sole parameter
and the body is immediately a match on exactly that parameter. -/
private meta def detectFunMatch? : Syntax → Option FunMatchToMatchFunMatch
  | stx@`(fun $x:ident => match $discr:ident with $alts:matchAlts) =>
    if discr.getId == x.getId then
      some { funStx := stx, matchAlts := alts }
    else none
  | _ => none

private meta def findFunMatchToMatchFun (stx : Syntax) : Array FunMatchToMatchFunMatch :=
  Syntax.collectAll
    (fun s =>
      match detectFunMatch? s with
      | some m => #[m]
      | none => #[])
    stx

private meta instance : Check FunMatchToMatchFunMatch where
  name := `funMatchToMatchFun
  severity := .information
  category := .simplification
  find := findFunMatchToMatchFun
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
