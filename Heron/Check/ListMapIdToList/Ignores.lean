module

meta import Heron.Assert
meta import Heron.Check.ListMapIdToList

#assertIgnore listMapIdToList in
example (xs : List Nat) : List Nat := xs.map (· + 1)
