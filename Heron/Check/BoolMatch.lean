import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure BoolMatchMatch where
  matchStx : Syntax
  matchKw : Syntax
  discr : Syntax
  trueRhs : Syntax
  falseRhs : Syntax

private def findBoolMatch : Syntax → Array BoolMatchMatch :=
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

@[check_rule]
instance : Check BoolMatchMatch where
  name := `boolMatch
  severity := .warning
  category := .simplification
  detect := fun stx => return findBoolMatch stx
  message := fun _ => m!"Use `if ... then ... else ...` instead of matching on `Bool`"
  emphasize := fun m => m.matchKw
  tags := #[.unnecessary]
  reference :=
    some
      { topic := "Bool conditionals",
        url := "https://lean-lang.org/functional_programming_in_lean/getting-to-know/conveniences.html" }
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

namespace Tests

#assertCheck boolMatch in
  def f (b : Bool) : Nat :=
    match b with
    | true => 1
    | false => 0 becomes
  `(def f (b : Bool) : Nat :=
      if b then 1 else 0)

#assertCheck boolMatch in
  def g (b : Bool) : Nat :=
    match b with
    | false => 0
    | true => 1 becomes
  `(def g (b : Bool) : Nat :=
      if b then 1 else 0)

#assertIgnore boolMatch in
  def h (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | _ => 2

#assertIgnore boolMatch in
  def k (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | 1 => 2
    | _ => 3

end Tests
