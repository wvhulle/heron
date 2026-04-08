import Heron.Check
import Heron.Assert

open Lean Elab Command Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure IntrosMatch where
  secondIntro : Syntax
  fullRange : Syntax
  allIntros : Array Syntax

private def collectIntroTactics : Syntax → Array Syntax :=
  Syntax.collectAll fun stx =>
    if stx.getKind == ``Lean.Parser.Tactic.intro then #[stx] else #[]

private def introIdents : Syntax → Array Syntax :=
  Syntax.collectAll fun stx =>
    if stx.isIdent || stx.getKind == ``Lean.Parser.Term.hole then #[stx] else #[]

private def detectIntros (stx : Syntax) : Array IntrosMatch :=
  let intros := collectIntroTactics stx
  if intros.size ≤ 1 then #[]
  else
    match mkSpan intros[0]! intros[intros.size - 1]! with
    | some fullRange => #[{ secondIntro := intros[1]!, fullRange, allIntros := intros }]
    | none => #[]

@[check_rule] instance : Check IntrosMatch where
  ruleName := `testIntros
  severity := .warning
  category := .simplification
  pureDetect := detectIntros
  message := fun _ => m!"Merge intros"
  node := fun m => m.secondIntro
  tags := #[.unnecessary]
  explanation := fun _ => m!"Multiple sequential `intro` tactics can be merged into one. This reduces tactic noise and is idiomatic Lean style."
  replacements := fun m => do
    let names : TSyntaxArray `ident := (m.allIntros.flatMap introIdents).map (⟨·⟩)
    let repl ← `(tactic| intro $names*)
    return #[{
      sourceNode := m.secondIntro
      targetNode := m.fullRange
      insertText := repl
      category := `tactic
      sourceLabel := m!"sequential intro"
    }]

namespace Tests

#assertIgnore testIntros in
example (a b : Nat) : a = a := rfl

#assertIgnore testIntros in
example : Nat → Nat → True := by intro a; exact trivial

#assertCheck testIntros in
example : Nat → Nat → True := by intro a; intro b; exact trivial
becomes `(example : Nat → Nat → True := by intro a b; exact trivial)

end Tests
