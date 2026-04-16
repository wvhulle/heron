module

meta import Heron.Assert
meta import Heron.Check.MatchToIfLet

#assertCheck matchToIfLet in
def f (x : Option Nat) : Nat := match x with | some v => v | _ => 0
becomes `(def f (x : Option Nat) : Nat := if let some v := x then v else 0)

-- Wildcard first
#assertCheck matchToIfLet in
def g (x : Option Nat) : Nat := match x with | _ => 0 | some v => v
becomes `(def g (x : Option Nat) : Nat := if let some v := x then v else 0)

-- Ignore: no wildcard arm
#assertIgnore matchToIfLet in
def h (x : Option Nat) : Nat := match x with | some v => v | none => 0

-- Ignore: more than 2 arms
#assertIgnore matchToIfLet in
def k (n : Nat) : Nat := match n with | 0 => 1 | 1 => 2 | _ => 3
