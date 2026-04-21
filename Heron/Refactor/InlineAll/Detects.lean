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

meta def metaAdd (a b : Nat) :=
  a + b

#assertRefactor inlineAllConst in
  example : Nat :=
    metaAdd 1 2 + metaAdd 3 4 becomes
  `(example : Nat :=
      (1 + 2) + (3 + 4))

private def privateAdd (a b : Nat) :=
  a + b

#assertRefactor inlineAllConst in
  example : Nat :=
    privateAdd 1 2 + privateAdd 3 4 becomes
  `(example : Nat :=
      (1 + 2) + (3 + 4))
