module

meta import Heron.Assert
meta import Heron.Check.ListFlattenOfMapToFlatMap

#assertCheck listFlattenOfMapToFlatMap in
example (f : Nat → List Nat) (xs : List Nat) : List Nat := List.flatten (List.map f xs)
becomes `(command|
example (f : Nat → List Nat) (xs : List Nat) : List Nat := List.flatMap f xs)

#assertCheck listFlattenOfMapToFlatMap in
example (f : Nat → List Nat) (xs : List Nat) : List Nat := (xs.map f).flatten
becomes `(command|
example (f : Nat → List Nat) (xs : List Nat) : List Nat := List.flatMap f xs)
