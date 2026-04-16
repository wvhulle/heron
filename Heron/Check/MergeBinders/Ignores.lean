module

meta import Heron.Assert
meta import Heron.Check.MergeBinders

#assertIgnore mergeBinders in
def g (x : Nat) (y : String) := toString x ++ y

#assertIgnore mergeBinders in
def h {x : Nat} {y : Nat} := x + y

-- Binders with default values must not be merged, since `(x y : Nat := 0)`
-- would apply the default to both names rather than just `x`.
#assertIgnore mergeBinders in
def i (x : Nat := 0) (y : Nat) := x + y
