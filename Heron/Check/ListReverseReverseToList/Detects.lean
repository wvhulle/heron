module

meta import Heron.Assert
meta import Heron.Check.ListReverseReverseToList

#assertCheck listReverseReverseToList in
example (xs : List Nat) : List Nat := List.reverse (List.reverse xs)
becomes `(command|
example (xs : List Nat) : List Nat := xs)

#assertCheck listReverseReverseToList in
example (xs ys : List Nat) : List Nat := (xs ++ ys).reverse.reverse
becomes `(command|
example (xs ys : List Nat) : List Nat := xs ++ ys)

#assertCheck listReverseReverseToList in
example (xs : List Nat) : List Nat := xs.reverse.reverse
becomes `(command|
example (xs : List Nat) : List Nat := xs)

#assertCheck listReverseReverseToList in
#eval List.reverse (List.reverse [1, 2])
becomes `(command|
#eval [1, 2])

#assertCheck listReverseReverseToList in
set_option linter.unusedVariables false in
example (xs ys : List Nat) : List Nat := xs.reverse.reverse
becomes `(command|
set_option linter.unusedVariables false in
example (xs ys : List Nat) : List Nat := xs)
