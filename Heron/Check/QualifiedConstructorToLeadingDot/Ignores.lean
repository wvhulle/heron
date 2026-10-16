module

meta import Heron.Assert
meta import Heron.Check.QualifiedConstructorToLeadingDot

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

#assertIgnore qualifiedConstructorToLeadingDot in
def leafSize := (BinTree.leaf : BinTree Nat).sizeOf

#assertIgnore qualifiedConstructorToLeadingDot in
def explicitLeaf : BinTree Nat := @BinTree.leaf Nat

#assertIgnore qualifiedConstructorToLeadingDot in
def alreadyDotted : BinTree Nat := .leaf

#assertIgnore qualifiedConstructorToLeadingDot in
def leafCount : BinTree Nat → Nat
  | .leaf => 1
  | .branch l _ r => leafCount l + leafCount r
