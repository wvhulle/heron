import Heron.Provider.Diagnostic
import Heron.AssertSuggests
import Heron.AssertEdits
import Heron.AssertNoSuggests

open Lean Elab Command Heron.Provider

private structure RflFixData where
  rflStx : Syntax

private partial def findRflTactics (stx : Syntax) : Array Syntax :=
  if let `(tactic| rfl) := stx then #[stx] else stx.getArgs.foldl (fun acc child => acc ++ findRflTactics child) #[]

@[diagnostic_rule] instance : Diagnostic RflFixData where
  ruleName := `testRfl
  severity := .information
  detect := fun stx => return (findRflTactics stx).map ({ rflStx := · })
  hintMessage := fun _ => m!"Use `exact rfl`."
  diagnosticMessage := m!"Bare `rfl` detected."
  replacements := fun fd => #[{
    sourceNode := fd.rflStx
    replacementNode := fd.rflStx
    replacementText := "exact rfl"
    sourceLabel := m!"bare rfl"
  }]
  diagnosticTags := #[.unnecessary]

namespace Tests

#assertNoSuggests testRfl in example (a : Nat) : a = a + 0 := by simp

#assertNoSuggests in
  example (a : Nat) : a = a :=
    rfl

#assertNoSuggests in
  example : True :=
    trivial

#assertSuggests testRfl`(tactic| rfl) => `(tactic| exact rfl) in example (a : Nat) : a = a := by rfl

#assertEdits testRfl`(tactic| rfl) => `(tactic| exact rfl) in example (a : Nat) : a = a := by rfl

end Tests
