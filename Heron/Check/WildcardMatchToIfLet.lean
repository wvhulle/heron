module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure WildcardMatchToIfLetMatch where
  matchStx : Syntax
  pat : TSyntax `term
  discr : TSyntax `term
  matchThroughFirstBar : Syntax
  firstArrow : Syntax
  wildcardArmHead : Syntax

private meta def wildcardArmHead? : TSyntax ``Term.matchAlt → Option Syntax
  | `(Term.matchAltExpr| |%$bar _ =>%$arrow $_) => some (mkNullNode #[bar, arrow])
  | _ => none

private meta def singlePatternArm? : TSyntax ``Term.matchAlt → Option (Syntax × TSyntax `term × Syntax)
  | `(Term.matchAltExpr| |%$bar $pat:term =>%$arrow $_) => some (bar, pat, arrow)
  | _ => none

private meta def detectMatchToIfLet? : Syntax → Option WildcardMatchToIfLetMatch
  | stx@`(match%$matchKw $discr:term with $patAlt:matchAlt $wildAlt:matchAlt) => do
    guard (wildcardArmHead? patAlt).isNone
    let (firstBar, pat, firstArrow) ← singlePatternArm? patAlt
    let wildcardArmHead ← wildcardArmHead? wildAlt
    return { matchStx := stx, pat, discr, matchThroughFirstBar := mkNullNode #[matchKw, firstBar],
             firstArrow, wildcardArmHead }
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
  replacements := some fun m => do
    let `(if%$ifKw let%$letKw $_ :=%$assignKw $_ then%$thenKw $_ else%$elseKw $_) ←
        `(if let x := y then x else y) | return #[]
    return #[
      { emphasizedSyntax := m.matchStx, oldSyntax := m.matchThroughFirstBar,
        newSyntax := mkNullNode #[ifKw, letKw], prettyPrint := printTokens,
        inlineViolationLabel := m!"match to if let" },
      { emphasizedSyntax := m.firstArrow, oldSyntax := m.firstArrow,
        newSyntax := mkNullNode #[assignKw, m.discr, thenKw], prettyPrint := printTokens,
        inlineViolationLabel := m!"the discriminant moves after the pattern" },
      { emphasizedSyntax := m.wildcardArmHead, oldSyntax := m.wildcardArmHead,
        newSyntax := elseKw, prettyPrint := printTokens,
        inlineViolationLabel := m!"wildcard arm becomes else" }]

register_check WildcardMatchToIfLetMatch
