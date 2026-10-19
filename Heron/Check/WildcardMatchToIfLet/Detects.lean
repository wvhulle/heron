module

meta import Heron.Assert
meta import Heron.Check.WildcardMatchToIfLet

#assertCheck wildcardMatchToIfLet in
def f (x : Option Nat) : Nat := match x with | some v => v | _ => 0
becomes `(def f (x : Option Nat) : Nat := if let some v := x then v else 0)

