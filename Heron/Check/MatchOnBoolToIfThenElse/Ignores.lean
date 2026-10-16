module

meta import Heron.Assert
meta import Heron.Check.MatchOnBoolToIfThenElse

#assertIgnore matchOnBoolToIfThenElse in
  def h (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | _ => 2

#assertIgnore matchOnBoolToIfThenElse in
  def k (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | 1 => 2
    | _ => 3

#assertIgnore matchOnBoolToIfThenElse in
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"
