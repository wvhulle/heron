import Heron.Assert
import Heron.Check.BoolMatchToIf

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

#assertIgnore boolMatchToIf in
  def h (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | _ => 2

#assertIgnore boolMatchToIf in
  def k (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | 1 => 2
    | _ => 3
