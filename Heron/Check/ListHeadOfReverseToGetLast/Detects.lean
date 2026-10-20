module

meta import Heron.Assert
meta import Heron.Check.ListHeadOfReverseToGetLast

#assertCheck listHeadOfReverseToGetLast in
example (xs : List Nat) : Option Nat := List.head? (List.reverse xs)
becomes `(command|
example (xs : List Nat) : Option Nat := xs.getLast?)

#assertCheck listHeadOfReverseToGetLast in
example (xs ys : List Nat) : Option Nat := (xs ++ ys).reverse.head?
becomes `(command|
example (xs ys : List Nat) : Option Nat := (xs ++ ys).getLast?)
