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

#assertRefactor inline in
example : Nat := myConst
becomes `(example : Nat := (42))

meta def metaDouble (n : Nat) :=
  n + n

#assertRefactor inline in
example : Nat := metaDouble 3
becomes `(example : Nat := (3 + 3))

private def privateConst :=
  7

#assertRefactor inline in
example : Nat := privateConst
becomes `(example : Nat := (7))
