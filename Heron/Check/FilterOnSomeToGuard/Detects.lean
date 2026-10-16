module

meta import Heron.Assert
meta import Heron.Check.FilterOnSomeToGuard

#assertCheck filterOnSomeToGuard in
example (xs : List Nat) (p : Nat → Bool) : Option Nat :=
  some xs.length |>.filter p
becomes `(example (xs : List Nat) (p : Nat → Bool) : Option Nat := (do
  guard (p xs.length)
  return xs.length))

#assertCheck filterOnSomeToGuard in
def filteredOrZero (x : Nat) : Nat := (some x |>.filter (· > 2) |>.getD 0)
becomes `(command| def filteredOrZero (x : Nat) : Nat := ((do
    guard ((· > 2) x)
    return x) |>.getD 0))
