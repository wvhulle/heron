module

meta import Heron.Assert
meta import Heron.Check.ListAnyOfMapToComposedAny

#assertCheck listAnyOfMapToComposedAny in
example (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) : Bool := List.any (List.map f xs) p
becomes `(command|
example (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) : Bool := xs.any (p ∘ f))

#assertCheck listAnyOfMapToComposedAny in
example (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) : Bool := (xs.map f).any p
becomes `(command|
example (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) : Bool := xs.any (p ∘ f))
