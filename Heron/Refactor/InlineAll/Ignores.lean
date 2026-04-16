module

meta import Heron.Assert
meta import Heron.Refactor.InlineAll

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
