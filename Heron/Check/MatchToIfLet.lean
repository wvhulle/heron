module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure MatchToIfLetMatch where
  matchStx : Syntax
  matchKw : Syntax
  pat : Syntax
  discr : Syntax
  thenRhs : Syntax
  elseRhs : Syntax

/-- Check if a match alt pattern is a wildcard `_`. -/
private meta def isWildcardAlt? (alt : Syntax) : Option Syntax :=
  let pats := alt[1]!  -- null-node of pattern groups
  if pats.getNumArgs != 1 then none
  else
    let patGroup := pats[0]!
    if patGroup.getNumArgs != 1 then none
    else
      let pat := patGroup[0]!
      if pat.isOfKind ``Term.hole || (pat.isIdent && pat.getId == `_) then
        some alt
      else none

private meta def detectMatchToIfLet? : Syntax → Option MatchToIfLetMatch
  | stx@`(match%$matchKw $discr:term with $alts:matchAlt*) => do
    guard (alts.size == 2)
    let a0 := alts[0]!.raw
    let a1 := alts[1]!.raw
    let (patAlt, wildAlt) ← match isWildcardAlt? a0, isWildcardAlt? a1 with
      | none, some _ => some (a0, a1)
      | some _, none => some (a1, a0)
      | _, _ => none
    return {
      matchStx := stx
      matchKw := matchKw
      pat := patAlt[1]![0]![0]!
      discr := discr.raw
      thenRhs := patAlt[3]!
      elseRhs := wildAlt[3]!
    }
  | _ => none

private meta def findMatchToIfLet : Syntax → Array MatchToIfLetMatch :=
  Syntax.collectAll fun stx =>
    match detectMatchToIfLet? stx with
    | some m => #[m]
    | none => #[]

private meta instance : Check MatchToIfLetMatch where
  name := `matchToIfLet
  severity := .information
  category := .style
  find := findMatchToIfLet
  message := fun _ => m!"Use `if let` instead of two-arm `match` with wildcard"
  emphasize := fun m => m.matchStx
  reference := some { topic := "if let", url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ => m!"A `match` with exactly two arms where one is `_` can be written more concisely as `if let`."
  replacements := fun m => do
    let pat : TSyntax `term := ⟨m.pat⟩
    let discr : TSyntax `term := ⟨m.discr⟩
    let thenRhs : TSyntax `term := ⟨m.thenRhs⟩
    let elseRhs : TSyntax `term := ⟨m.elseRhs⟩
    let repl ← `(if let $pat := $discr then $thenRhs else $elseRhs)
    return #[{
      emphasizedSyntax := m.matchStx
      oldSyntax := m.matchStx
      newSyntax := repl
      inlineViolationLabel := m!"match to if let"
    }]

meta initialize Check.register (α := MatchToIfLetMatch)
