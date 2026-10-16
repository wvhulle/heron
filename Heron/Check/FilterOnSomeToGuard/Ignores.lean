module

meta import Heron.Assert
meta import Heron.Check.FilterOnSomeToGuard

-- Plain `Option.map`, not the some/filter pattern.
#assertIgnore filterOnSomeToGuard in
example (x : Nat) (f : Nat → Nat) : Option Nat := some x |>.map f

-- Filter on an arbitrary Option, not on a freshly-wrapped value.
#assertIgnore filterOnSomeToGuard in
example (o : Option Nat) (p : Nat → Bool) : Option Nat := o.filter p
