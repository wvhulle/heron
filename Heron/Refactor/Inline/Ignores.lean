module

meta import Heron.Assert
meta import Heron.Refactor.Inline

-- The definition site of `d` should not flag `d` itself for inlining.
#assertIgnore inline in
  def d :=
    0

-- Recursive definitions must not be offered for inlining — expanding them
-- would loop.
def rec1 : Nat → Nat
  | 0 => 0
  | n + 1 => rec1 n

#assertIgnore inline in
example : Nat := rec1 5

-- Instances should not be inlined.
instance : ToString Bool where
  toString := fun b => if b then "yes" else "no"

#assertIgnore inline in
example : String := toString true
