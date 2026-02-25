import Heron.Provider.Diagnostic
import Heron.AssertSuggests
import Heron.AssertEdits
import Heron.AssertNoSuggests

open Lean Elab Command Heron.Provider

/-- Create a `Syntax` spanning two syntax nodes. -/
private def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure IntrosFixData where
  secondIntro : Syntax
  fullRange : Syntax
  replacement : String

private partial def collectIntroTactics (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Tactic.intro then #[stx]
  else stx.getArgs.foldl (fun acc c => acc ++ collectIntroTactics c) #[]

private partial def introIdents (stx : Syntax) : Array Syntax :=
  if stx.isIdent || stx.getKind == ``Lean.Parser.Term.hole then #[stx]
  else stx.getArgs.foldl (fun acc c => acc ++ introIdents c) #[]

private def detectIntros (stx : Syntax) : Array IntrosFixData :=
  let intros := collectIntroTactics stx
  if intros.size ≤ 1 then #[]
  else
    let names := (intros.foldl (fun acc s => acc ++ introIdents s) #[]).map (·.getId.toString)
    let combined := "intro " ++ " ".intercalate names.toList
    match mkSpan intros[0]! intros[intros.size - 1]! with
    | some fullRange => #[{ secondIntro := intros[1]!, fullRange, replacement := combined }]
    | none => #[]

instance : Diagnostic IntrosFixData where
  ruleName := `testIntros
  severity := .warning
  detect := fun stx => return (detectIntros stx)
  sourceNode := (·.secondIntro)
  hintMessage := m!"Combine intros."
  diagnosticMessage := m!"Sequential intros."
  replacementText := (·.replacement)
  replacementNode := (·.fullRange)
  diagnosticTags := #[.unnecessary]

register_diagnostic IntrosFixData

namespace Tests

#assertNoSuggests testIntros in
example (a b : Nat) : a = a := rfl

#assertNoSuggests testIntros in
example : Nat → Nat → True := by intro a; exact trivial

#assertEdits testIntros `(tactic| intro a; intro b) => `(tactic| intro a b) in
example : Nat → Nat → True := by intro a; intro b; exact trivial

end Tests
