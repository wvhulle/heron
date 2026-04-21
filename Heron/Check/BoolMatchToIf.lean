module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure BoolMatchToIfMatch where
  matchStx : Syntax
  matchKw : Syntax
  discr : Syntax
  trueRhs : Syntax
  falseRhs : Syntax

private meta def findBoolMatchToIf : Syntax → Array BoolMatchToIfMatch :=
  Syntax.collectAll fun
    |
    stx@`(match $discr:term with
          | true => $rhs1:term
          | false => $rhs2:term) =>
      #[{ matchStx := stx, matchKw := stx[0]!, discr, trueRhs := rhs1, falseRhs := rhs2 }]
    |
    stx@`(match $discr:term with
          | false => $rhs1:term
          | true => $rhs2:term) =>
      #[{ matchStx := stx, matchKw := stx[0]!, discr, trueRhs := rhs2, falseRhs := rhs1 }]
    | _ => #[]

private meta instance : Check BoolMatchToIfMatch where
  name := `boolMatchToIf
  severity := .warning
  category := .simplification
  detect := fun stx => return findBoolMatchToIf stx
  message := fun _ => m!"Use `if ... then ... else ...` instead of matching on `Bool`"
  emphasize := fun m => m.matchKw
  tags := #[.unnecessary]
  reference := none
  explanation := fun _ =>
    m!"Pattern matching on `true`/`false` can be written as `if ... then ... else ...`, which is more concise and idiomatic."
  replacements := fun m => do
    let discr : TSyntax `term := ⟨m.discr⟩
    let trueRhs : TSyntax `term := ⟨m.trueRhs⟩
    let falseRhs : TSyntax `term := ⟨m.falseRhs⟩
    let repl ← `(if $discr then $trueRhs else $falseRhs)
    return #[{
          emphasizedSyntax := m.matchStx
          oldSyntax := m.matchStx
          newSyntax := repl
          inlineViolationLabel := m!"bool match" }]

meta initialize Check.register (α := BoolMatchToIfMatch)
