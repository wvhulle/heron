module

meta import Heron.Assert
meta import Heron.Check.MergeIntros

#assertIgnore mergeIntros in
  example (a _b : Nat) : a = a :=
    rfl

#assertIgnore mergeIntros in example : Nat → Nat → True := by intro a; exact trivial

-- Intros separated by other tactics must NOT be merged — the rule would
-- otherwise drop the intervening tactic when rewriting.
#assertIgnore mergeIntros in
example : Nat → True → True := by
  intro a
  skip
  intro b
  exact b

#assertIgnore mergeIntros in
example : Nat → Nat → True := by
  intro (x : Nat)
  intro y
  exact trivial

#assertIgnore mergeIntros in
example : Nat × Nat → Nat → True := by
  intro ⟨a, b⟩
  intro c
  exact trivial

#assertIgnore mergeIntros in
example : Nat → Nat → True := by
  intro
  intro x
  exact trivial
