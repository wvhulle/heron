module

meta import Heron.Assert
meta import Heron.Check.PureBindToApplication

#assertCheck pureBindToApplication in
example (f : Nat → Option Nat) (n : Nat) : Option Nat := pure n >>= f
becomes `(command|
example (f : Nat → Option Nat) (n : Nat) : Option Nat := f n)
