module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure MergeMatchArmsWithSameBodyMatch where
  secondArm : Syntax
  /-- A null node wrapping the arms of `run`; its `getRange?` covers the span. -/
  fullRange : Syntax
  run : Array (TSyntax ``Term.matchAlt)

private meta def sharesRhs (prev next : TSyntax ``Term.matchAlt) : Bool :=
  match prev, next with
  | `(Term.matchAltExpr| | $_ => $rhs1), `(Term.matchAltExpr| | $_ => $rhs2) => rhs1 == rhs2
  | _, _ => false

private meta def runWithSharedRhs? (run : List (TSyntax ``Term.matchAlt)) :
    Option MergeMatchArmsWithSameBodyMatch := do
  guard (run.length ≥ 2)
  let arms := run.toArray
  let secondArm : TSyntax ``Term.matchAlt ← arms[1]?
  return {
    secondArm
    fullRange := mkNullNode (arms.map (·.raw))
    run := arms
  }

private meta instance : Check MergeMatchArmsWithSameBodyMatch where
  name := `mergeMatchArmsWithSameBody
  description := "Suggests merging match arms whose right-hand sides are identical."
  kinds := #[``Term.match]
  severity := .information
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | `(match $_:term with
          $alts:matchAlt*) =>
      (alts.toList.splitBy sharesRhs).toArray.filterMap runWithSharedRhs?
    | _ => #[]
  message := fun _ => m!"Merge match arms with identical right-hand sides"
  emphasize := fun m => m.fullRange
  tags := #[.unnecessary]
  sources := #[.functionalProgrammingInLean "Or-patterns" "Monads/Additional-Conveniences/#or-patterns"]
  explanation := fun _ => m!"Consecutive match arms with the same body can be merged using `|` patterns."
  replacements := some fun m => do
    let some (firstArm : TSyntax ``Term.matchAlt) := m.run[0]? | return #[]
    let `(Term.matchAltExpr| | $_ => $rhs) := firstArm | return #[]
    let alternatives := m.run.flatMap fun
      | `(Term.matchAltExpr| | $[$patss,*]|* => $_) => patss
      | _ => #[]
    let repl ← `(Term.matchAltExpr| | $[$alternatives,*]|* => $rhs)
    return #[{
      emphasizedSyntax := m.secondArm
      oldSyntax := m.fullRange
      newSyntax := repl
      inlineViolationLabel := m!"duplicate arm"
      category := `matchAlt
    }]

register_check MergeMatchArmsWithSameBodyMatch
