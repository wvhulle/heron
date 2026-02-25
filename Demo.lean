import Heron.Rules

/-!# Test out fixing violations and refactors

-/

set_option linter.heron true

example (n : Nat) : n = n := by rfl

example (a b : Nat) (_ : a = b) : a = a := by
  rfl

-- set_option linter.testIntros false in
example : Nat → Nat → Nat → True := by
  intro a
  intro b
  intro c
  exact trivial

def greeting :=
  "hello"

def add1 (n : Nat) :=
  n + 1

example : String :=
  greeting

example : Nat :=
  add1 7

example : String :=
  let a := false
  if !a then "No a" else "Yes a"
