module

meta import Heron.Assert
meta import Heron.Check.ListHeadOfReverseToGetLast

#assertIgnore listHeadOfReverseToGetLast in
example (xs : List Nat) : Option Nat := xs.head?
