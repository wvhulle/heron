module

meta import Heron.Assert
meta import Heron.Check.RemoveIdRunWithoutEffects

-- Ignore: has mut (imperative)
#assertIgnore removeIdRunWithoutEffects in
example : Nat := Id.run do
  let mut x := 5
  x := x + 1
  return x

-- Ignore: has for loop
#assertIgnore removeIdRunWithoutEffects in
example : Nat := Id.run do
  let mut sum := 0
  for x in [1, 2, 3] do
    sum := sum + x
  return sum

-- Ignore: has early return (doIf)
#assertIgnore removeIdRunWithoutEffects in
example : Nat := Id.run do
  if true then return 1
  return 2

#assertIgnore removeIdRunWithoutEffects in
def pureTail (x : Nat) : Nat := Id.run do pure x
