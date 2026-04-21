module

meta import Heron.Assert
meta import Heron.Check.ConsecutiveAltsToOrPattern

#assertCheck consecutiveAltsToOrPattern in
  def f (x : Bool) : Nat :=
    match x with
    | true => 1
    | false => 1 becomes
  `(def f (x : Bool) : Nat :=
      match x with
      | true | false => 1)
