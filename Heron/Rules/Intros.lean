import Heron.Diagnostic
import Heron.Assert

open Lean Elab Command Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure IntrosFixData where
  secondIntro : Syntax
  fullRange : Syntax
  replacement : String

private def collectIntroTactics : Syntax → Array Syntax :=
  Syntax.collectAll fun stx =>
    if stx.getKind == ``Lean.Parser.Tactic.intro then #[stx] else #[]

private def introIdents : Syntax → Array Syntax :=
  Syntax.collectAll fun stx =>
    if stx.isIdent || stx.getKind == ``Lean.Parser.Term.hole then #[stx] else #[]

private def detectIntros (stx : Syntax) : Array IntrosFixData :=
  let intros := collectIntroTactics stx
  if intros.size ≤ 1 then #[]
  else
    let names := (intros.foldl (fun acc s => acc ++ introIdents s) #[]).map (·.getId.toString)
    let combined := "intro " ++ " ".intercalate names.toList
    match mkSpan intros[0]! intros[intros.size - 1]! with
    | some fullRange => #[{ secondIntro := intros[1]!, fullRange, replacement := combined }]
    | none => #[]

@[diagnostic_rule] instance : Diagnostic IntrosFixData where
  ruleName := `testIntros
  severity := .warning
  category := .simplification
  detect := fun stx => return (detectIntros stx)
  shortInstruction := fun _ => m!"Merge intros"
  violationNode := fun fd => fd.secondIntro
  diagnosticTags := #[.unnecessary]
  longInstruction := fun fd => m!"Multiple sequential `intro` tactics can be merged into `{fd.replacement}`. This reduces tactic noise and is idiomatic Lean style."
  replacements := fun fd => #[{
    sourceNode := fd.secondIntro
    targetNode := fd.fullRange
    insertText := fd.replacement
    sourceLabel := m!"sequential intro"
  }]

namespace Tests

#assertIgnore testIntros in
example (a b : Nat) : a = a := rfl

#assertIgnore testIntros in
example : Nat → Nat → True := by intro a; exact trivial

#assertFix testIntros `(tactic| intro a; intro b) => `(tactic| intro a b) in
example : Nat → Nat → True := by intro a; intro b; exact trivial

end Tests
