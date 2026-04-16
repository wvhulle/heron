import Heron.Assert
import Heron.Check.MergeBinders

#assertCheck mergeBinders in
def f (x : Nat) (y : Nat) := x + y
becomes `(def f (x y : Nat) := x + y)

#assertIgnore mergeBinders in
def g (x : Nat) (y : String) := toString x ++ y

#assertIgnore mergeBinders in
def h {x : Nat} {y : Nat} := x + y
