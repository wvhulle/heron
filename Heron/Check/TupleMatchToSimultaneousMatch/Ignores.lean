module

meta import Heron.Assert
meta import Heron.Check.TupleMatchToSimultaneousMatch

#assertIgnore tupleMatchToSimultaneousMatch in
  def g (x y : Nat) : Nat :=
    match x, y with
    | a, b => a + b

#assertIgnore tupleMatchToSimultaneousMatch in
  def h (p : Nat × Nat) : Nat :=
    match p with
    | (a, b) => a + b
