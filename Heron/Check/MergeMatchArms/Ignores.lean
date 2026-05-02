module

meta import Heron.Assert
meta import Heron.Check.MergeMatchArms

#assertIgnore mergeMatchArms in
  def g (x : Bool) : Nat :=
    match x with
    | true => 1
    | false => 0

-- Same rhs but the matching arms are not adjacent.
#assertIgnore mergeMatchArms in
  def g2 (n : Nat) : Nat :=
    match n with
    | 0 => 1
    | 1 => 0
    | 2 => 1

-- Single-arm match: nothing to merge.
#assertIgnore mergeMatchArms in
  def g3 (x : Bool) : Nat :=
    match x with
    | _ => 0

-- Distinct rhs expressions that happen to evaluate to the same value.
#assertIgnore mergeMatchArms in
  def g4 (n : Nat) : Nat :=
    match n with
    | 0 => 1 + 0
    | 1 => 0 + 1
