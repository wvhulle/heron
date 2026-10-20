module

meta import Heron.Assert
meta import Heron.Check.ListAllOfMapToComposedAll

#assertCheck listAllOfMapToComposedAll in
example (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) : Bool := List.all (List.map f xs) p
becomes `(command|
example (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) : Bool := xs.all (p ∘ f))

#assertCheck listAllOfMapToComposedAll in
example (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) : Bool := (xs.map f).all p
becomes `(command|
example (f : Nat → Nat) (p : Nat → Bool) (xs : List Nat) : Bool := xs.all (p ∘ f))
