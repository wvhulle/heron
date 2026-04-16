module

meta import Heron.Assert
meta import Heron.Check.RflToExactRfl

#assertCheck rflToExactRfl in
example (a : Nat) : a = a := by rfl
becomes `(example (a : Nat) : a = a := by exact rfl)

-- `rfl` appearing after another tactic should still be flagged.
#assertCheck rflToExactRfl in
example (a : Nat) : a = a := by skip; rfl
becomes `(example (a : Nat) : a = a := by skip; exact rfl)
