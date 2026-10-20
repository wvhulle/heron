module

meta import Heron.Assert
meta import Heron.Check.BindPureToArgument

#assertCheck bindPureToArgument in
example (o : Option Nat) : Option Nat := o >>= pure
becomes `(command|
example (o : Option Nat) : Option Nat := o)
