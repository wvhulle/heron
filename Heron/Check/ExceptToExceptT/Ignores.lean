module

meta import Heron.Assert
meta import Heron.Check.ExceptToExceptT

-- No outer monad wrapping — plain Except
#assertIgnore exceptToExceptT in
  def k : Except String Nat :=
    sorry
