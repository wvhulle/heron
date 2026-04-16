module

meta import Heron.Assert
meta import Heron.Check.MergeIntros

#assertIgnore mergeIntros in
  example (a b : Nat) : a = a :=
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
