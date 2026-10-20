module

meta import Heron.Assert
meta import Heron.Check.FunctorIdMapToArgument

#assertCheck functorIdMapToArgument in
example (o : Option Nat) : Option Nat := id <$> o
becomes `(command|
example (o : Option Nat) : Option Nat := o)
