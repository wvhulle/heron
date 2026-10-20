module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure WildcardMatchToIfLetMatch where
  matchStx : Syntax
  pat : TSyntax `term
  discr : TSyntax `term
  thenRhs : TSyntax `term
  elseRhs : TSyntax `term

private meta def wildcardArmRhs? : TSyntax ``Term.matchAlt → Option (TSyntax `term)
  | `(Term.matchAltExpr| | _ => $rhs) => some rhs
  | _ => none

private meta def singlePatternArm? : TSyntax ``Term.matchAlt → Option (TSyntax `term × TSyntax `term)
  | `(Term.matchAltExpr| | $pat:term => $rhs) => some (pat, rhs)
  | _ => none

private meta def detectMatchToIfLet? : Syntax → Option WildcardMatchToIfLetMatch
  | stx@`(match $discr:term with $patAlt:matchAlt $wildAlt:matchAlt) => do
    guard (wildcardArmRhs? patAlt).isNone
    let (pat, thenRhs) ← singlePatternArm? patAlt
    let elseRhs ← wildcardArmRhs? wildAlt
    return { matchStx := stx, pat, discr, thenRhs, elseRhs }
  | _ => none

private meta instance : Check WildcardMatchToIfLetMatch where
  name := `wildcardMatchToIfLet
  description := "Suggests `if let` instead of a two-arm `match` whose second arm is a wildcard."
  kinds := #[``Term.match]
  severity := .information
  category := .style
  detect := fun stx => do
    let some m := detectMatchToIfLet? stx | return #[]
    unless ← bindsVariables m.pat do return #[]
    return #[m]
  message := fun _ => m!"Use `if let` instead of two-arm `match` with wildcard"
  emphasize := fun m => m.matchStx
  sources := #[.functionalProgrammingInLean "if let" "Getting-to-Know-Lean/Additional-Conveniences/#if-let"]
  explanation := fun _ =>
    m!"When only one constructor of a sum type is of interest, `if let pat := e then … else …` \
       states that directly, and in some contexts reads better than a two-arm `match` with a \
       wildcard."
  replacements := some fun m => return #[{
    emphasizedSyntax := m.matchStx
    oldSyntax := m.matchStx
    newSyntax := ← `(if let $m.pat := $m.discr then $m.thenRhs else $m.elseRhs)
    inlineViolationLabel := m!"match to if let" }]

register_check WildcardMatchToIfLetMatch
