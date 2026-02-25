import Heron.Rules.Basic

open Lean Elab Command Heron.Rules

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

instance : Rule IntrosFixData where
  ruleName := `testIntros
  severity := .warning
  detect := fun stx => return (detectIntros stx)
  diagnosticNode := (·.secondIntro)
  hintMessage := m!"Combine intros."
  diagnosticMessage := m!"Sequential intros."
  replacementText := (·.replacement)
  replacementNode := (·.fullRange)
  diagnosticTags := #[.unnecessary]

initialize Rule.initOption (α := IntrosFixData)
initialize Rule.addLinter (α := IntrosFixData)

namespace Tests

#eval Rule.addLinter (α := IntrosFixData)

#assertNoSuggests testIntros in
example (a b : Nat) : a = a := rfl

#assertNoSuggests testIntros in
example : Nat → Nat → True := by intro a; exact trivial

#assertEdits testIntros `(tactic| intro a; intro b) => `(tactic| intro a b) in
example : Nat → Nat → True := by intro a; intro b; exact trivial

end Tests
