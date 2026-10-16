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

#assertCheck natLiteralPatterns in
def headPredecessor (l : List Nat) : Nat := match l with
  | Nat.succ n :: _ => n
  | _ => 0
becomes `(command| def headPredecessor (l : List Nat) : Nat := match l with
  | (n + 1) :: _ => n
  | _ => 0)

#assertCheck natLiteralPatterns in
def minusTwo (m : Nat) : Nat := match m with
  | Nat.succ (Nat.succ n) => n
  | _ => 0
becomes `(command| def minusTwo (m : Nat) : Nat := match m with
  | n + 2 => n
  | _ => 0)

#assertCheck natLiteralPatterns in
def isOne (m : Nat) : Bool := match m with
  | Nat.succ Nat.zero => true
  | _ => false
becomes `(command| def isOne (m : Nat) : Bool := match m with
  | 1 => true
  | _ => false)
