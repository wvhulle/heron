module

meta import Heron.Assert
meta import Heron.Check.NestedMonadToTransformer

-- No outer monad wrapping — plain Option
#assertIgnore nestedMonadToTransformer in
  def h : Option Nat :=
    sorry

-- No outer monad wrapping — plain Except
#assertIgnore nestedMonadToTransformer in
  def k : Except String Nat :=
    sorry

-- Same-constructor nesting belongs to NestedMonadJoin, not this check
#assertIgnore nestedMonadToTransformer in
  def l : Option (Option Nat) :=
    sorry
