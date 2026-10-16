module

meta import Heron.Assert
meta import Heron.Check.QualifiedConstructorToLeadingDot

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

#assertCheck qualifiedConstructorToLeadingDot in
def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)
becomes `(command| def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l))

#assertCheck qualifiedConstructorToLeadingDot in
def parseDigit (c : Char) : Except String Nat :=
  if c.isDigit then Except.ok (c.toNat - '0'.toNat) else Except.error "not a digit"
becomes `(command| def parseDigit (c : Char) : Except String Nat :=
  if c.isDigit then .ok (c.toNat - '0'.toNat) else .error "not a digit")
