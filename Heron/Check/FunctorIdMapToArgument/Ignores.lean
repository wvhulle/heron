module

meta import Heron.Assert
meta import Heron.Check.FunctorIdMapToArgument

#assertIgnore functorIdMapToArgument in
example (f : Nat → Nat) (o : Option Nat) : Option Nat := f <$> o
