module

meta import Heron.Assert
meta import Heron.Check.OptionWrapFilter

#assertCheck optionWrapFilter in
example (xs : List Nat) (p : Nat → Bool) : Option Nat :=
  some xs.length |>.filter p
becomes `(example (xs : List Nat) (p : Nat → Bool) : Option Nat := do
  guard (p xs.length)
  return xs.length)
