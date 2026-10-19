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

#assertCheck removeMutWithoutReassignment in
example : Nat := Id.run do
  let mut x := 5
  let f := fun (x : Nat) => Id.run do
    let mut y := x
    y := y + 1
    return y
  return f x
becomes `(
example : Nat := Id.run do
  let x := 5
  let f := fun (x : Nat) => Id.run do
    let mut y := x
    y := y + 1
    return y
  return f x)
