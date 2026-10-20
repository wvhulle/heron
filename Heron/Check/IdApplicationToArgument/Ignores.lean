module

meta import Heron.Assert
meta import Heron.Check.IdApplicationToArgument

#assertIgnore idApplicationToArgument in
example (f : Nat → Nat) (n : Nat) : Nat := f n

#assertIgnore idApplicationToArgument in
example (xs : List Nat) : List Nat := xs.map id
