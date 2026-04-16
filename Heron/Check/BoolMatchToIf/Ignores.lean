module

meta import Heron.Assert
meta import Heron.Check.BoolMatchToIf

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
