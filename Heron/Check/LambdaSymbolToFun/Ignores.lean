module

meta import Heron.Assert
meta import Heron.Check.LambdaSymbolToFun

#assertIgnore lambdaSymbolToFun in
def increment : Nat → Nat := fun x => x + 1
