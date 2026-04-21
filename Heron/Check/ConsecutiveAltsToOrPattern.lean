module

public meta import Heron.Check

open Lean Elab Command Parser Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private meta def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure ConsecutiveAltsToOrPatternMatch where
  secondArm : Syntax
  fullRange : Syntax
  firstAlt : Syntax
  secondAlt : Syntax

private meta def matchConsecutivePair? (prev next : Syntax) : Option ConsecutiveAltsToOrPatternMatch := do
  let `(Term.matchAltExpr| | $_ => $rhs1) := prev | none
  let `(Term.matchAltExpr| | $_ => $rhs2) := next | none
  guard (rhs1 == rhs2)
  let fullRange ← mkSpan prev next
  return { secondArm := next, fullRange, firstAlt := prev, secondAlt := next }

private meta def findConsecutiveAltsToOrPatternInAlts : List Syntax → Array ConsecutiveAltsToOrPatternMatch
  | prev :: next :: rest =>
    let acc := findConsecutiveAltsToOrPatternInAlts (next :: rest)
    match matchConsecutivePair? prev next with
    | some m => acc.push m
    | none => acc
  | _ => #[]

private meta def findConsecutiveAltsToOrPattern : Syntax → Array ConsecutiveAltsToOrPatternMatch :=
  Syntax.collectAll fun
    |
    `(match $_:term with
        $alts:matchAlt*) =>
      findConsecutiveAltsToOrPatternInAlts (alts.map (·.raw) |>.toList)
    | _ => #[]

@[check_rule] private meta instance : Check ConsecutiveAltsToOrPatternMatch where
  name := `consecutiveAltsToOrPattern
  severity := .information
  category := .simplification
  detect := fun stx => return findConsecutiveAltsToOrPattern stx
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
