module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure MergeMatchArmsMatch where
  secondArm : Syntax
  /-- A null node wrapping `firstAlt` and `secondAlt`; its `getRange?` covers the span. -/
  fullRange : Syntax
  firstAlt : Syntax
  secondAlt : Syntax

private meta def pairWithSharedRhs? (prev next : Syntax) : Option MergeMatchArmsMatch := do
  let `(Term.matchAltExpr| | $_ => $rhs1) := prev | none
  let `(Term.matchAltExpr| | $_ => $rhs2) := next | none
  guard (rhs1 == rhs2)
  return {
    secondArm := next
    fullRange := mkNullNode #[prev, next]
    firstAlt := prev
    secondAlt := next
  }

private meta def findMergeMatchArms : Syntax → Array MergeMatchArmsMatch :=
  Syntax.collectAll fun
    |
    `(match $_:term with
        $alts:matchAlt*) =>
      let l := (alts.map (·.raw)).toList
      ((l.zip l.tail).filterMap fun (a, b) => pairWithSharedRhs? a b).toArray
    | _ => #[]

private meta instance : Check MergeMatchArmsMatch where
  name := `mergeMatchArms
  severity := .information
  category := .simplification
  detect := fun stx => return findMergeMatchArms stx
  message := fun _ => m!"Merge match arms with identical right-hand sides"
  emphasize := fun m => m.fullRange
  tags := #[.unnecessary]
  reference := some { topic := "Or-patterns", url := "https://leanprover.github.io/functional_programming_in_lean/monads/conveniences.html" }
  explanation := fun _ => m!"Consecutive match arms with the same body can be merged using `|` patterns."
  replacements := fun m => do
    let `(Term.matchAltExpr| | $pat1 => $rhs) := m.firstAlt | return #[]
    let `(Term.matchAltExpr| | $pat2 => $_) := m.secondAlt | return #[]
    let repl ← `(Term.matchAltExpr| | $pat1 | $pat2 => $rhs)
    return #[{
      emphasizedSyntax := m.secondArm
      oldSyntax := m.fullRange
      newSyntax := repl
      inlineViolationLabel := m!"duplicate arm"
      category := `matchAlt
    }]

meta initialize Check.register (α := MergeMatchArmsMatch)
