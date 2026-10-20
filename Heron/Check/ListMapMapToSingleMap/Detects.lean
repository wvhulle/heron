module

meta import Heron.Assert
meta import Heron.Check.ListMapMapToSingleMap

#assertCheck listMapMapToSingleMap in
example (f g : Nat → Nat) (xs : List Nat) : List Nat := List.map f (List.map g xs)
becomes `(command|
example (f g : Nat → Nat) (xs : List Nat) : List Nat := List.map (f ∘ g) xs)

#assertCheck listMapMapToSingleMap in
example (f g : Nat → Nat) (xs : List Nat) : List Nat := (xs.map g).map f
becomes `(command|
example (f g : Nat → Nat) (xs : List Nat) : List Nat := List.map (f ∘ g) xs)

#assertCheck listMapMapToSingleMap in
example (f g : Nat → Nat) (xs : List Nat) : List Nat := xs.map g |>.map f
becomes `(command|
example (f g : Nat → Nat) (xs : List Nat) : List Nat := List.map (f ∘ g) xs)
