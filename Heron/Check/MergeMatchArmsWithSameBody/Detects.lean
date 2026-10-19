module

meta import Heron.Assert
meta import Heron.Check.MergeMatchArmsWithSameBody

#assertCheck mergeMatchArmsWithSameBody in
  def f (x : Bool) : Nat :=
    match x with
    | true => 1
    | false => 1 becomes
  `(def f (x : Bool) : Nat :=
    match x with
    | true | false => 1)

-- First two of three arms share an rhs.
#assertCheck mergeMatchArmsWithSameBody in
  def f2 (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | 1 => 1
    | _ => 0 becomes
  `(def f2 (n : Nat) : Nat :=
    match n with
    | 0 | 1 => 1
    | _ => 0)

-- Last two of three arms share an rhs.
#assertCheck mergeMatchArmsWithSameBody in
  def f3 (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | 1 => 0
    | 2 => 0 becomes
  `(def f3 (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | 1 | 2 => 0)

-- Constructor patterns from an ADT.
#assertCheck mergeMatchArmsWithSameBody in
  def f4 (x : Option Nat) : Nat :=
    match x with
    | none => 0
    | some 0 => 0
    | some _ => 1 becomes
  `(def f4 (x : Option Nat) : Nat :=
    match x with
    | none | some 0 => 0
    | some _ => 1)

#assertCheck mergeMatchArmsWithSameBody in
def threeArms (n : Nat) : Nat := match n with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | _ => 0
becomes `(command| def threeArms (n : Nat) : Nat := match n with
  | 0 | 1 | 2 => 5
  | _ => 0)

private inductive Shape where
  | circle (r : Nat)
  | square (r : Nat)
  | dot

#assertCheck mergeMatchArmsWithSameBody in
def radius (s : Shape) : Nat := match s with
  | .circle r => r + 1
  | .square r => r + 1
  | .dot => 0
becomes `(command| def radius (s : Shape) : Nat := match s with
  | .circle r | .square r => r + 1
  | .dot => 0)
