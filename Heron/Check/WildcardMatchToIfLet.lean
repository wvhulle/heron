module

public meta import Heron.Check
meta import Heron.Register

set_option linter.sourcePositionInRule false

open Lean Elab Command Parser Heron

private structure WildcardMatchToIfLetMatch where
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

private meta def detectMatchToIfLet? : Syntax → Option WildcardMatchToIfLetMatch
  | stx@`(match%$matchKw $discr:term with $a0:matchAlt $a1:matchAlt) => do
    let (patAlt, wildAlt) ← match wildcardArmRhs? a0, wildcardArmRhs? a1 with
      | none, some _ => some (a0, a1)
      | some _, none => some (a1, a0)
      | _, _ => none
    let (pat, thenRhs) ← singlePatternArm? patAlt
    let elseRhs ← wildcardArmRhs? wildAlt
    return { matchStx := stx, matchKw, pat, discr, thenRhs, elseRhs }
  | _ => none

private meta def patternBindsVariable (pat : Syntax) : CommandElabM Bool := do
  let some range := pat.getRange? | return false
  let trees ← collectInfoTrees pat
  return (trees.flatMap collectTermInfos).any fun (_, ti) =>
    ti.isBinder && ti.stx.getRange?.any fun r => range.start ≤ r.start && r.stop ≤ range.stop

private meta instance : Check WildcardMatchToIfLetMatch where
  name := `wildcardMatchToIfLet
  description := "Suggests `if let` instead of a two-arm `match` whose second arm is a wildcard."
  kinds := #[``Term.match]
  severity := .information
  category := .style
  detect := fun stx => do
    let some m := detectMatchToIfLet? stx | return #[]
    unless ← patternBindsVariable m.pat do return #[]
    return #[m]
  message := fun _ => m!"Use `if let` instead of two-arm `match` with wildcard"
  emphasize := fun m => m.matchStx
  sources := #[.functionalProgrammingInLean "if let" "Getting-to-Know-Lean/Additional-Conveniences/#if-let"]
  explanation := fun _ =>
    m!"When only one constructor of a sum type is of interest, `if let pat := e then … else …` \
       states that directly, and in some contexts reads better than a two-arm `match` with a \
       wildcard."
  replacements := some fun m => do
    let repl ← `(if let $m.pat := $m.discr then $m.thenRhs else $m.elseRhs)
    return #[{
      emphasizedSyntax := m.matchStx
      oldSyntax := m.matchStx
      newSyntax := repl
      inlineViolationLabel := m!"match to if let"
    }]

register_check WildcardMatchToIfLetMatch
