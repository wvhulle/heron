module

meta import Heron.Assert
meta import Heron.Check.FunctorMapMapToSingleMap

#assertIgnore functorMapMapToSingleMap in
example (f : Nat → Nat) (o : Option Nat) : Option Nat := f <$> o

#assertIgnore functorMapMapToSingleMap in
example (f g : Nat → Nat) (xs : Array Nat) : Array Nat := f <$> g <$> xs
