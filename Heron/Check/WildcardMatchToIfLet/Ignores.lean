module

meta import Heron.Assert
meta import Heron.Check.WildcardMatchToIfLet

-- Ignore: no wildcard arm
#assertIgnore wildcardMatchToIfLet in
def h (x : Option Nat) : Nat := match x with | some v => v | none => 0

#assertIgnore wildcardMatchToIfLet in
def literalPattern (n : Nat) : Nat := match n with | 0 => 1 | _ => 2

#assertIgnore wildcardMatchToIfLet in
def wildcardFirst (x : Option Nat) : Nat := match x with | _ => 0 | some v => v

-- Ignore: more than 2 arms
#assertIgnore wildcardMatchToIfLet in
def k (n : Nat) : Nat := match n with | 0 => 1 | 1 => 2 | _ => 3
