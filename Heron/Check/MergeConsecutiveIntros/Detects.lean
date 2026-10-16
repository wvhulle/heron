module

meta import Heron.Assert
meta import Heron.Check.MergeConsecutiveIntros

#assertCheck mergeConsecutiveIntros in example : Nat → Nat → True := by intro a; intro b; exact trivial becomes
  `(example : Nat → Nat → True := by intro a b; exact trivial)

-- Three consecutive intros collapse into one.
#assertCheck mergeConsecutiveIntros in example : Nat → Nat → Nat → True := by
  intro a
  intro b
  intro c
  exact trivial
becomes `(example : Nat → Nat → Nat → True := by
  intro a b c
  exact trivial)

-- Holes are preserved in the merged intro.
#assertCheck mergeConsecutiveIntros in example : Nat → Nat → True := by intro a; intro _; exact trivial
becomes `(example : Nat → Nat → True := by intro a _; exact trivial)
