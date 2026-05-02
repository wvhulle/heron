module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure BoolMatchToIfMatch where
  matchStx : Syntax
  matchKw : Syntax
  discr : Syntax
  trueRhs : Syntax
  falseRhs : Syntax

private meta instance : Check BoolMatchToIfMatch
    where
  name := `boolMatchToIf
  kinds := #[``Term.match]
  severity := .warning
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | `(match%$matchKw $discr:term with
        | true => $rhs1:term
        | false => $rhs2:term) =>
      #[{ matchStx := stx, matchKw := matchKw, discr, trueRhs := rhs1, falseRhs := rhs2 }]
    | `(match%$matchKw $discr:term with
        | false => $rhs1:term
        | true => $rhs2:term) =>
      #[{ matchStx := stx, matchKw := matchKw, discr, trueRhs := rhs2, falseRhs := rhs1 }]
    | _ => #[]
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

meta initialize
  Check.register (α := BoolMatchToIfMatch)
