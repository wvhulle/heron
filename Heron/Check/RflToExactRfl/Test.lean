module

meta import Heron.Assert
meta import Heron.Check.RflToExactRfl

#assertIgnore rflToExactRfl in example (a : Nat) : a = a + 0 := by simp

#assertCheck rflToExactRfl in
example (a : Nat) : a = a := by rfl
becomes `(example (a : Nat) : a = a := by exact rfl)
