module

meta import Heron.Assert
meta import Heron.Check.ListMapMapToSingleMap

#assertIgnore listMapMapToSingleMap in
example (f : Nat → Nat) (xs : List Nat) : List Nat := List.map f xs

#assertIgnore listMapMapToSingleMap in
example (f : Nat → Nat) (xs ys : List Nat) : List Nat := List.map f (xs ++ ys)

#assertIgnore listMapMapToSingleMap in
example (f g : Nat → Nat) (xs : List Nat) : List Nat := List.map (f ∘ g) xs
