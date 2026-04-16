module

meta import Heron.Assert
meta import Heron.Check.TupleMatchToSimultaneous

#assertCheck tupleMatchToSimultaneous in
  def f (x y : Nat) : Nat :=
    match (x, y) with
    | (a, b) => a + b becomes
  `(def f (x y : Nat) : Nat :=
      match x, y with
      | a, b => a + b)
