module

meta import Heron.Assert
meta import Heron.Check.MergeBinders

#assertCheck mergeBinders in
def f (x : Nat) (y : Nat) := x + y
becomes `(def f (x y : Nat) := x + y)

-- A grouped binder (`(a b : Nat)`) followed by a single-name binder of the same
-- type should still be merged into one group.
#assertCheck mergeBinders in
def g (a b : Nat) (c : Nat) := a + b + c
becomes `(def g (a b c : Nat) := a + b + c)
