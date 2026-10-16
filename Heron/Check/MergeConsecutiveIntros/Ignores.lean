module

meta import Heron.Assert
meta import Heron.Check.MergeConsecutiveIntros

#assertIgnore mergeConsecutiveIntros in
  example (a _b : Nat) : a = a :=
    rfl

#assertIgnore mergeConsecutiveIntros in example : Nat → Nat → True := by intro a; exact trivial

-- Intros separated by other tactics must NOT be merged — the rule would
-- otherwise drop the intervening tactic when rewriting.
#assertIgnore mergeConsecutiveIntros in
example : Nat → True → True := by
  intro a
  skip
  intro b
  exact b

#assertIgnore mergeConsecutiveIntros in
example : Nat → Nat → True := by
  intro (x : Nat)
  intro y
  exact trivial

#assertIgnore mergeConsecutiveIntros in
example : Nat × Nat → Nat → True := by
  intro ⟨a, b⟩
  intro c
  exact trivial

#assertIgnore mergeConsecutiveIntros in
example : Nat → Nat → True := by
  intro
  intro x
  exact trivial
