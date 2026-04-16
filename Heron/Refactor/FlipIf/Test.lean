module

meta import Heron.Assert
meta import Heron.Refactor.FlipIf

#assertRefactor flipIf in
def flipMe (p : Bool) (a b : Nat) : Nat := if !p then a else b
becomes `(def flipMe (p : Bool) (a b : Nat) : Nat := if p then b else a)

#assertIgnore flipIf in
def noFlip (p : Bool) (a b : Nat) : Nat := if p then a else b

#assertRefactor flipIf in
example : String :=
  let a := false
  if !a then "No a" else "Yes a"
becomes `(command|
example : String :=
  let a := false
  if a then "Yes a" else "No a")
