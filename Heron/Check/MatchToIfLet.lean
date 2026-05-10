module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure MatchToIfLetMatch where
  matchStx : Syntax
  matchKw : Syntax
  pat : TSyntax `term
  discr : TSyntax `term
  thenRhs : TSyntax `term
  elseRhs : TSyntax `term

/-- Recognise a wildcard match arm `| _ => rhs`, returning its RHS. -/
private meta def wildcardArmRhs? : TSyntax ``Term.matchAlt → Option (TSyntax `term)
  | `(Term.matchAltExpr| | _ => $rhs) => some rhs
  | _ => none

/-- Recognise a single-pattern arm `| pat => rhs`. -/
private meta def singlePatternArm? :
    TSyntax ``Term.matchAlt → Option (TSyntax `term × TSyntax `term)
  | `(Term.matchAltExpr| | $pat:term => $rhs) => some (pat, rhs)
  | _ => none

private meta def detectMatchToIfLet? : Syntax → Option MatchToIfLetMatch
  | stx@`(match%$matchKw $discr:term with $a0:matchAlt $a1:matchAlt) => do
    let (patAlt, wildAlt) ← match wildcardArmRhs? a0, wildcardArmRhs? a1 with
      | none, some _ => some (a0, a1)
      | some _, none => some (a1, a0)
      | _, _ => none
    let (pat, thenRhs) ← singlePatternArm? patAlt
    let elseRhs ← wildcardArmRhs? wildAlt
    return { matchStx := stx, matchKw, pat, discr, thenRhs, elseRhs }
  | _ => none

private meta instance : Check MatchToIfLetMatch where
  name := `matchToIfLet
  kinds := #[``Term.match]
  severity := .information
  category := .style
  detect := fun stx => pure <|
    match detectMatchToIfLet? stx with
    | some m => #[m]
    | none => #[]
  message := fun _ => m!"Use `if let` instead of two-arm `match` with wildcard"
  emphasize := fun m => m.matchStx
  reference := some { topic := "if let", url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ => m!"A `match` with exactly two arms where one is `_` can be written more concisely as `if let`."
  replacements := fun m => do
    let repl ← `(if let $m.pat := $m.discr then $m.thenRhs else $m.elseRhs)
    return #[{
      emphasizedSyntax := m.matchStx
      oldSyntax := m.matchStx
      newSyntax := repl
      inlineViolationLabel := m!"match to if let"
    }]

meta initialize Check.register (α := MatchToIfLetMatch)
