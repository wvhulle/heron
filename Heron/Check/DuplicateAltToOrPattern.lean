import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure DuplicateAltToOrPatternMatch where
  secondArm : Syntax
  fullRange : Syntax
  firstAlt : Syntax
  secondAlt : Syntax

/-- Reprint a matchAlt's pattern portion (everything between | and =>). -/
private def altPatsText (alt : Syntax) : String :=
  reprintTrimmed alt[1]!

/-- Reprint a matchAlt's RHS. -/
private def altRhsText (alt : Syntax) : String :=
  reprintTrimmed alt[3]!

private def findDuplicateAltToOrPatternInAlts (alts : Array Syntax) : Array DuplicateAltToOrPatternMatch :=
  if alts.size < 2 then #[]
  else
    (List.range (alts.size - 1)).foldl (init := #[]) fun acc i =>
      let a1 := alts[i]!
      let a2 := alts[i + 1]!
      if altRhsText a1 == altRhsText a2 then
        match mkSpan a1 a2 with
        | some fullRange =>
          acc.push { secondArm := a2, fullRange, firstAlt := a1, secondAlt := a2 }
        | none => acc
      else acc

private def findDuplicateAltToOrPattern : Syntax → Array DuplicateAltToOrPatternMatch :=
  Syntax.collectAll fun stx =>
    if stx.getKind != ``Term.match then #[]
    else
      let matchAlts := stx[5]!
      let alts := matchAlts[0]!.getArgs
      findDuplicateAltToOrPatternInAlts alts

@[check_rule] instance : Check DuplicateAltToOrPatternMatch where
  name := `duplicateAltToOrPattern
  severity := .information
  category := .simplification
  detect := fun stx => return findDuplicateAltToOrPattern stx
  message := fun _ => m!"Merge match arms with identical right-hand sides"
  emphasize := fun m => m.fullRange
  tags := #[.unnecessary]
  reference := some { topic := "Or-patterns", url := "https://leanprover.github.io/functional_programming_in_lean/monads/conveniences.html" }
  explanation := fun _ => m!"Consecutive match arms with the same body can be merged using `|` patterns."
  replacements := fun m => do
    let pat1 : TSyntax `term := ⟨m.firstAlt[1]!⟩
    let pat2 : TSyntax `term := ⟨m.secondAlt[1]!⟩
    let rhs : TSyntax `term := ⟨m.firstAlt[3]!⟩
    let repl ← `(Term.matchAltExpr| | $pat1 | $pat2 => $rhs)
    return #[{
      emphasizedSyntax := m.secondArm
      oldSyntax := m.fullRange
      newSyntax := repl
      inlineViolationLabel := m!"duplicate arm"
      category := `matchAlt
    }]

namespace Tests

#assertCheck duplicateAltToOrPattern in
def f (x : Bool) : Nat := match x with
  | true => 1
  | false => 1
becomes `(def f (x : Bool) : Nat := match x with
  | true | false => 1)

#assertIgnore duplicateAltToOrPattern in
def g (x : Bool) : Nat := match x with
  | true => 1
  | false => 0

end Tests
