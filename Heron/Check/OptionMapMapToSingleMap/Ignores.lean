module

meta import Heron.Assert
meta import Heron.Check.OptionMapMapToSingleMap

#assertIgnore optionMapMapToSingleMap in
example (f : Nat → Nat) (o : Option Nat) : Option Nat := o.map f

#assertIgnore optionMapMapToSingleMap in
example (f g : Nat → Nat) (o : Option Nat) : Option Nat := f <$> g <$> o
