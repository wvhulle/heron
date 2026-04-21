module

meta import Heron.Assert
meta import Heron.Check.ConsecutiveAltsToOrPattern

#assertIgnore consecutiveAltsToOrPattern in
  def g (x : Bool) : Nat :=
    match x with
    | true => 1
    | false => 0
