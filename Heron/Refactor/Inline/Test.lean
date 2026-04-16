module

meta import Heron.Assert
meta import Heron.Refactor.Inline

def double (n : Nat) :=
  n + n

#assertRefactor inline in
example : Nat := double 3
becomes `(example : Nat := (3 + 3))

def myConst :=
  42

-- The definition site of `d` should not flag `d` itself for inlining.
#assertIgnore inline in
  def d :=
    0

#assertRefactor inline in
example : Nat := myConst
becomes `(example : Nat := (42))
