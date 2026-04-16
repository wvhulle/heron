module

meta import Heron.Assert
meta import Heron.Check.UnnecessaryIdRun

-- Simple return
#assertCheck unnecessaryIdRun in
example : Nat := Id.run do return 42
becomes `(example : Nat := 42)

-- Let + return same variable collapses
#assertCheck unnecessaryIdRun in
example : Nat := Id.run do
  let x := 5
  return x
becomes `(example : Nat := 5)
