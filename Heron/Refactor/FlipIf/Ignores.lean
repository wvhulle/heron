module

meta import Heron.Assert
meta import Heron.Refactor.FlipIf

#assertIgnore flipIf in
def noFlip (p : Bool) (a b : Nat) : Nat := if p then a else b
