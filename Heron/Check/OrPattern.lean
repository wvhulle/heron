import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure OrPatternMatch where
  secondArm : Syntax
  fullRange : Syntax
  replacement : String

/-- Reprint a matchAlt's pattern portion (everything between | and =>). -/
private def altPatsText (alt : Syntax) : String :=
  reprintTrimmed alt[1]!

/-- Reprint a matchAlt's RHS. -/
private def altRhsText (alt : Syntax) : String :=
  reprintTrimmed alt[3]!

private def findOrPatternsInAlts (alts : Array Syntax) : Array OrPatternMatch :=
  if alts.size < 2 then #[]
  else
    (List.range (alts.size - 1)).foldl (init := #[]) fun acc i =>
      let a1 := alts[i]!
      let a2 := alts[i + 1]!
      if altRhsText a1 == altRhsText a2 then
        match mkSpan a1 a2 with
        | some fullRange =>
          let merged := s!"| {altPatsText a1} | {altPatsText a2} => {altRhsText a1}"
          acc.push { secondArm := a2, fullRange, replacement := merged }
        | none => acc
      else acc

private def findOrPatterns : Syntax → Array OrPatternMatch :=
  Syntax.collectAll fun stx =>
    if stx.getKind != ``Term.match then #[]
    else
      let matchAlts := stx[5]!
      let alts := matchAlts[0]!.getArgs
      findOrPatternsInAlts alts

@[check_rule] instance : Check OrPatternMatch where
  ruleName := `orPattern
  severity := .information
  category := .simplification
  detect := fun stx => return findOrPatterns stx
  message := fun _ => m!"Merge match arms with identical right-hand sides"
  node := fun m => m.secondArm
  tags := #[.unnecessary]
  reference := some { topic := "Or-patterns", url := "https://lean-lang.org/functional_programming_in_lean/monads/conveniences.html" }
  explanation := fun _ => m!"Consecutive match arms with the same body can be merged using `|` patterns."
  replacements := fun m => #[{
    sourceNode := m.secondArm
    targetNode := m.fullRange
    insertText := m.replacement
    sourceLabel := m!"duplicate arm"
  }]

namespace Tests

#assertCheck orPattern in
def f (x : Bool) : Nat := match x with
  | true => 1
  | false => 1
becomes `(command| def f (x : Bool) : Nat := match x with
  | true | false => 1)

#assertIgnore orPattern in
def g (x : Bool) : Nat := match x with
  | true => 1
  | false => 0

end Tests
