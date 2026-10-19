module

meta import Heron.Assert
meta import Heron.Check.LambdaSymbolToFun

#assertIgnore lambdaSymbolToFun in
def increment : Nat → Nat := fun x => x + 1

#assertIgnore lambdaSymbolToFun in
def incrementWithMapsto : Nat → Nat := fun x ↦ x + 1

#assertIgnore lambdaSymbolToFun in
def predecessor : Nat → Option Nat := fun
  | 0 => none
  | n + 1 => some n
