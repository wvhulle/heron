module

meta import Heron.Assert
meta import Heron.Check.RemoveMutWithoutReassignment

-- Unused mut: x is never reassigned
#assertCheck removeMutWithoutReassignment in
example : Nat := Id.run do
  let mut x := 5
  return x + 1
becomes `(
example : Nat := Id.run do
  let x := 5
  return x + 1)
