module

meta import Heron.Assert
meta import Heron.Check.BoolMatchToIf

#assertCheck boolMatchToIf in
  def f (b : Bool) : Nat :=
    match b with
    | true => 1
    | false => 0 becomes
  `(def f (b : Bool) : Nat :=
      if b then 1 else 0)

#assertCheck boolMatchToIf in
  def g (b : Bool) : Nat :=
    match b with
    | false => 0
    | true => 1 becomes
  `(def g (b : Bool) : Nat :=
      if b then 1 else 0)
