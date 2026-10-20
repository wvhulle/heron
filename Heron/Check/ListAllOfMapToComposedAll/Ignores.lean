module

meta import Heron.Assert
meta import Heron.Check.ListAllOfMapToComposedAll

#assertIgnore listAllOfMapToComposedAll in
example (p : Nat → Bool) (xs : List Nat) : Bool := xs.all p
