module

meta import Heron.Assert
meta import Heron.Check.ListMapIdToList

#assertCheck listMapIdToList in
example (xs : List Nat) : List Nat := List.map id xs
becomes `(command|
example (xs : List Nat) : List Nat := xs)

#assertCheck listMapIdToList in
example (xs : List Nat) : List Nat := xs.map id
becomes `(command|
example (xs : List Nat) : List Nat := xs)
