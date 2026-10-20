module

meta import Heron.Assert
meta import Heron.Check.IdApplicationToArgument

#assertCheck idApplicationToArgument in
example (n : Nat) : Nat := id (n + 1)
becomes `(command|
example (n : Nat) : Nat := n + 1)

#assertCheck idApplicationToArgument in
example (n : Nat) : Int := id n
becomes `(command|
example (n : Nat) : Int := ↑n)
