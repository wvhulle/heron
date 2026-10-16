module

meta import Heron.Assert
meta import Heron.Check.RemoveMutWithoutReassignment

-- Ignore: x IS reassigned
#assertIgnore removeMutWithoutReassignment in
example : Nat := Id.run do
  let mut x := 5
  x := x + 1
  return x

-- Ignore: no mut at all
#assertIgnore removeMutWithoutReassignment in
example : Nat := Id.run do
  let x := 5
  return x

#assertIgnore removeMutWithoutReassignment in
def reassignedByArrow : IO Nat := do
  let mut x := 0
  x ← pure 1
  return x

#assertIgnore removeMutWithoutReassignment in
def reassignedByPattern : Nat := Id.run do
  let mut a := 0
  let mut b := 0
  (a, b) := (1, 2)
  return a + b
