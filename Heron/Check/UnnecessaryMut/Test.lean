import Heron.Assert
import Heron.Check.UnnecessaryMut

-- Unused mut: x is never reassigned
#assertCheck unnecessaryMut in
example : Nat := Id.run do
  let mut x := 5
  return x + 1
becomes `(
example : Nat := Id.run do
  let x := 5
  return x + 1)

-- Ignore: x IS reassigned
#assertIgnore unnecessaryMut in
example : Nat := Id.run do
  let mut x := 5
  x := x + 1
  return x

-- Ignore: no mut at all
#assertIgnore unnecessaryMut in
example : Nat := Id.run do
  let x := 5
  return x
