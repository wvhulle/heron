module

meta import Heron.Assert
meta import Heron.Check.MergeBinders

#assertIgnore mergeBinders in
def g (x : Nat) (y : String) := toString x ++ y

#assertIgnore mergeBinders in
def h {x : Nat} {y : Nat} := x + y
