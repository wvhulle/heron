module

meta import Heron.Assert
meta import Heron.Check.MergeMatchArms

#assertCheck mergeMatchArms in
  def f (x : Bool) : Nat :=
    match x with
    | true => 1
    | false => 1 becomes
  `(def f (x : Bool) : Nat :=
      match x with
      | true | false => 1)

-- First two of three arms share an rhs.
#assertCheck mergeMatchArms in
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
#assertCheck mergeMatchArms in
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
#assertCheck mergeMatchArms in
  def f4 (x : Option Nat) : Nat :=
    match x with
    | none => 0
    | some 0 => 0
    | some _ => 1 becomes
  `(def f4 (x : Option Nat) : Nat :=
      match x with
      | none | some 0 => 0
      | some _ => 1)
