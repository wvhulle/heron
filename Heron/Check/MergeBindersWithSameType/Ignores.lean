module

meta import Heron.Assert
meta import Heron.Check.MergeBindersWithSameType

#assertIgnore mergeBindersWithSameType in
def g (x : Nat) (y : String) := toString x ++ y

#assertIgnore mergeBindersWithSameType in
def h {x : Nat} {y : Nat} := x + y

-- Binders with default values must not be merged, since `(x y : Nat := 0)`
-- would apply the default to both names rather than just `x`.
#assertIgnore mergeBindersWithSameType in
def i (x : Nat := 0) (y : Nat) := x + y
