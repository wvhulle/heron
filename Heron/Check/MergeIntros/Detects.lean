module

meta import Heron.Assert
meta import Heron.Check.MergeIntros

#assertCheck mergeIntros in example : Nat → Nat → True := by intro a; intro b; exact trivial becomes
  `(example : Nat → Nat → True := by intro a b; exact trivial)
