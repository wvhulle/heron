module

meta import Heron.Assert
meta import Heron.Check.NatLiteralPatterns

-- Ignore: already using numeric patterns
#assertIgnore natLiteralPatterns in
def g (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => k
