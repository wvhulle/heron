module

meta import Heron.Assert
meta import Heron.Refactor.InlineAll

def triple (n : Nat) :=
  n + n + n

#assertRefactor inlineAllConst in
  example : Nat :=
    triple 2 + triple 3 becomes
  `(example : Nat :=
      (2 + 2 + 2) + (3 + 3 + 3))
