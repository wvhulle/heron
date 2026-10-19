module

meta import Heron.Assert
meta import Heron.Check.NatConstructorsToLiterals

#assertCheck natConstructorsToLiterals in
def f (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ k => k
becomes `(def f (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => k)

#assertCheck natConstructorsToLiterals in
def headPredecessor (l : List Nat) : Nat := match l with
  | Nat.succ n :: _ => n
  | _ => 0
becomes `(command| def headPredecessor (l : List Nat) : Nat := match l with
  | (n + 1) :: _ => n
  | _ => 0)

#assertCheck natConstructorsToLiterals in
def minusTwo (m : Nat) : Nat := match m with
  | Nat.succ (Nat.succ n) => n
  | _ => 0
becomes `(command| def minusTwo (m : Nat) : Nat := match m with
  | n + 2 => n
  | _ => 0)

#assertCheck natConstructorsToLiterals in
def isOne (m : Nat) : Bool := match m with
  | Nat.succ Nat.zero => true
  | _ => false
becomes `(command| def isOne (m : Nat) : Bool := match m with
  | 1 => true
  | _ => false)

#assertCheck natConstructorsToLiterals in
def halve : Nat → Nat
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve n + 1
becomes `(command| def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1)

#assertCheck natConstructorsToLiterals in
def five : Nat := Nat.succ 4
becomes `(command| def five : Nat := 5)

#assertCheck natConstructorsToLiterals in
def doubledSuccessor (n : Nat) : Nat := Nat.succ n * 2
becomes `(command| def doubledSuccessor (n : Nat) : Nat := (n + 1) * 2)

#assertCheck natConstructorsToLiterals in
def successors (xs : List Nat) : List Nat := xs.map Nat.succ
becomes `(command| def successors (xs : List Nat) : List Nat := xs.map (· + 1))

#assertCheck natConstructorsToLiterals in
open Nat in
def viaOpenNamespace (n : Nat) : Nat := succ n
becomes `(command| open Nat in
def viaOpenNamespace (n : Nat) : Nat := n + 1)
