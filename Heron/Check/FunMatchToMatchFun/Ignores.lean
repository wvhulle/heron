module

meta import Heron.Assert
meta import Heron.Check.FunMatchToMatchFun

-- Ignore: multiple parameters
#assertIgnore funMatchToMatchFun in
  def g := fun x y =>
    match x with
    | 0 => y
    | _ =>
      0

-- Ignore: match on different variable
#assertIgnore funMatchToMatchFun in
  def h (y : Nat) := fun x =>
    match y with
    | 0 => x
    | _ =>
      0

-- Ignore: already using fun | syntax
#assertIgnore funMatchToMatchFun in
  def k := fun
    | 0 => "zero"
    | _ => "other"
