module

meta import Heron.Assert
meta import Heron.Check.NatLiteralPatterns

#assertCheck natLiteralPatterns in
def f (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ k => k
becomes `(def f (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => k)

-- Ignore: already using numeric patterns
#assertIgnore natLiteralPatterns in
def g (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => k
