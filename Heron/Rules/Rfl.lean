import Heron.Rules.Basic

open Lean Elab Command Heron.Rules

private structure RflFixData where
  rflStx : Syntax

private partial def findRflTactics (stx : Syntax) : Array Syntax :=
  if let `(tactic| rfl) := stx then #[stx] else stx.getArgs.foldl (fun acc child => acc ++ findRflTactics child) #[]

instance : Rule RflFixData where
  name := `testRfl
  severity := .information
  detect := fun stx => return (findRflTactics stx).map ({ rflStx := · })
  diagStx := (·.rflStx)
  hintMsg := m!"Use `exact rfl`."
  diagMsg := m!"Bare `rfl` detected."
  toSuggestion := fun d => { suggestion := "exact rfl", span? := some d.rflStx }

initialize
  Rule.initOption (α := RflFixData)
initialize
  Rule.addLinter (α := RflFixData)

namespace Tests

#eval Rule.addLinter (α := RflFixData)

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
