module

meta import Heron.Assert
meta import Heron.Refactor.InlineAll

def triple (n : Nat) :=
  n + n + n

#assertRefactor inlineAllConst in
  example : Nat :=
    triple 2 + triple 3 becomes
  `(example : Nat :=
      (2 + 2 + 2) + (3 + 3 + 3))

def myVal :=
  10

#assertIgnore inlineAllConst in
  example : Nat :=
    myVal

#assertIgnore inlineAllConst in
  def unused :=
    42

#assertIgnore inlineAllConst in
  def recFn : Nat → Nat
    | 0 => 0
    | n + 1 => recFn n
