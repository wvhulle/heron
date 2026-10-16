module

meta import Heron.Assert
meta import Heron.Check.NatConstructorsToLiterals

-- Ignore: already using numeric patterns
#assertIgnore natConstructorsToLiterals in
def g (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => k

#assertIgnore natConstructorsToLiterals in
theorem succEqAddOne (n : Nat) : Nat.succ n = n + 1 := rfl
