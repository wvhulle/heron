module

meta import Heron.Assert
meta import Heron.Check.MergeBinders

#assertCheck mergeBinders in
def f (x : Nat) (y : Nat) := x + y
becomes `(def f (x y : Nat) := x + y)
