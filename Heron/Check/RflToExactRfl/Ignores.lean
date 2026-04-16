module

meta import Heron.Assert
meta import Heron.Check.RflToExactRfl

#assertIgnore rflToExactRfl in example (a : Nat) : a = a + 0 := by simp

-- Already in `exact rfl` form — nothing to rewrite.
#assertIgnore rflToExactRfl in
example (a : Nat) : a = a := by exact rfl
