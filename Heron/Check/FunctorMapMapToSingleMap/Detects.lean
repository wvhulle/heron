module

meta import Heron.Assert
meta import Heron.Check.FunctorMapMapToSingleMap

#assertCheck functorMapMapToSingleMap in
example (f g : Nat → Nat) (o : Option Nat) : Option Nat := f <$> g <$> o
becomes `(command|
example (f g : Nat → Nat) (o : Option Nat) : Option Nat := (fun a => f (g a)) <$> o)
