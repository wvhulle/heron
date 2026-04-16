module

meta import Heron.Assert
meta import Heron.Check.FunMatchToMatchFun

#assertCheck funMatchToMatchFun in
  def f := fun x =>
    match x with
    | 0 => "zero"
    | _ => "other" becomes
  `(def f := fun
      | 0 => "zero"
      | _ => "other")
