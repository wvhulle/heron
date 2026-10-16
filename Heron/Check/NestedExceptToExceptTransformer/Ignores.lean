module

meta import Heron.Assert
meta import Heron.Check.NestedExceptToExceptTransformer

-- No outer monad wrapping — plain Except
#assertIgnore nestedExceptToExceptTransformer in
  def k : Except String Nat :=
    sorry
