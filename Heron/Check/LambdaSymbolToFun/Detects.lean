module

meta import Heron.Assert
meta import Heron.Check.LambdaSymbolToFun

#assertCheck lambdaSymbolToFun in
def increment : Nat → Nat := λ x => x + 1
becomes `(command| def increment : Nat → Nat := fun x => x + 1)

#assertCheck lambdaSymbolToFun in
def predecessor : Nat → Option Nat := λ
  | 0 => none
  | n + 1 => some n
becomes `(command| def predecessor : Nat → Option Nat := fun
  | 0 => none
  | n + 1 => some n)
