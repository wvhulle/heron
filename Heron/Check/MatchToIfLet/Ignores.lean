module

meta import Heron.Assert
meta import Heron.Check.MatchToIfLet

-- Ignore: no wildcard arm
#assertIgnore matchToIfLet in
def h (x : Option Nat) : Nat := match x with | some v => v | none => 0

-- Ignore: more than 2 arms
#assertIgnore matchToIfLet in
def k (n : Nat) : Nat := match n with | 0 => 1 | 1 => 2 | _ => 3
