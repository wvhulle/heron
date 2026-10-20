module

meta import Heron.Assert
meta import Heron.Check.OptionMapMapToSingleMap

#assertCheck optionMapMapToSingleMap in
example (f g : Nat → Nat) (o : Option Nat) : Option Nat := Option.map f (Option.map g o)
becomes `(command|
example (f g : Nat → Nat) (o : Option Nat) : Option Nat := Option.map (f ∘ g) o)

#assertCheck optionMapMapToSingleMap in
example (f g : Nat → Nat) (o : Option Nat) : Option Nat := (o.map g).map f
becomes `(command|
example (f g : Nat → Nat) (o : Option Nat) : Option Nat := Option.map (f ∘ g) o)

#assertCheck optionMapMapToSingleMap in
example (f g : Nat → Nat) (o : Option Nat) : Option Nat := f <$> g <$> o
becomes `(command|
example (f g : Nat → Nat) (o : Option Nat) : Option Nat := Option.map (f ∘ g) o)
