import AssertSuggests
import Test.Linters

/-! ## Tests -/

-- No suggestions for clean examples
#assertNoSuggests testRfl in
example (a : Nat) : a = a + 0 := by simp

#assertNoSuggests in
example (a : Nat) : a = a := rfl

#assertNoSuggests in
example : True := trivial

-- Single-line suggestion: rfl → exact rfl
#assertSuggests testRfl `(tactic| rfl) => `(tactic| exact rfl) in
example (a : Nat) : a = a := by rfl

-- Multiline suggestion: sequential intros → combined intro
#assertSuggests testIntros `(tactic| intro x
  intro y) => `(tactic| intro x y) in
example : ∀ x y : Nat, x = x := by
  intro x
  intro y
  rfl
