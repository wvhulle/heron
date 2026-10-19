module

meta import Heron.Assert
meta import Heron.Check.WildcardMatchToIfLet

#assertCheck wildcardMatchToIfLet in
def f (x : Option Nat) : Nat := match x with | some v => v | _ => 0
becomes `(def f (x : Option Nat) : Nat := if let some v := x then v else 0)

#assertCheck wildcardMatchToIfLet in
def firstLarge (x : Option Nat) : Bool :=
  match x with
  | some v =>
    -- keep this comment
    v >= 10
  | _ => false
becomes `(command| def firstLarge (x : Option Nat) : Bool :=
  if let some v := x then
    -- keep this comment
    v >= 10
  else false)

#assertCheck wildcardMatchToIfLet in
def bothSome (x y : Option Nat) : Nat :=
  match x with
  | some a =>
    match y with
    | some b => a + b
    | _ => a
  | _ => 0
becomes `(command| def bothSome (x y : Option Nat) : Nat :=
  if let some a := x then
    if let some b := y then a + b
    else a
  else 0)

