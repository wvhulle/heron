module

meta import Heron.Assert
meta import Heron.Check.MergeIntros

#assertIgnore mergeIntros in
  example (a b : Nat) : a = a :=
    rfl

#assertIgnore mergeIntros in example : Nat → Nat → True := by intro a; exact trivial
