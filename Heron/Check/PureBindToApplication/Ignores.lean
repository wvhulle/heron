module

meta import Heron.Assert
meta import Heron.Check.PureBindToApplication

#assertIgnore pureBindToApplication in
example (f : Nat → Option Nat) (o : Option Nat) : Option Nat := o >>= f

#assertIgnore pureBindToApplication in
example (f : Nat → Option Nat) (n : Nat) : Option Nat := do
  let m ← pure n
  f m
