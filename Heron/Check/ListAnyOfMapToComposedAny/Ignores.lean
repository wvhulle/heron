module

meta import Heron.Assert
meta import Heron.Check.ListAnyOfMapToComposedAny

#assertIgnore listAnyOfMapToComposedAny in
example (p : Nat → Bool) (xs : List Nat) : Bool := xs.any p
