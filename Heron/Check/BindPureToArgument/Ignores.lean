module

meta import Heron.Assert
meta import Heron.Check.BindPureToArgument

#assertIgnore bindPureToArgument in
example (f : Nat → Option Nat) (o : Option Nat) : Option Nat := o >>= f
