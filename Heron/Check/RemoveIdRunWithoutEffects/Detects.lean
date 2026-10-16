module

meta import Heron.Assert
meta import Heron.Check.RemoveIdRunWithoutEffects

-- Simple return
#assertCheck removeIdRunWithoutEffects in
example : Nat := Id.run do return 42
becomes `(example : Nat := 42)

-- Let + return same variable collapses
#assertCheck removeIdRunWithoutEffects in
example : Nat := Id.run do
  let x := 5
  return x
becomes `(example : Nat := 5)
