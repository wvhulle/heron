import Heron.Rules

set_option linter.heron true
set_option heron.profile true

example (n : Nat) : n = n := by rfl

example (a b : Nat) (_ : a = b) : a = a := by
  rfl

-- set_option linter.mergeIntros false in
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
  if !a then "No a"
  else
    "Yes a"

-- IdRunTrivial: should warn (trivial Id.run do)
example : Nat :=
  Id.run
    (do
      return 42)

-- UnusedMut: should warn (x is never reassigned)
example : Nat :=
  Id.run
    (do
      let mut x := 5
      return x + 1)

-- No warning: legitimate imperative code
example : Nat :=
  Id.run
    (do
      let mut x := 0
      for _ in [1, 2, 3]do
        x := x + 1
      return x)

-- BoolMatch: should warn (match on true/false)
def boolToNat (b : Bool) : Nat :=
  match b with
  | true => 1
  | false =>
    0

-- OrPattern: should inform (duplicate RHS)
def orPatternDemo (x : Bool) : Nat :=
  match x with
  | true => 42
  | false =>
    42

-- SharedBinder: should inform (same type)
def addNats (x : Nat) (y : Nat) :=
  x + y

-- BindToDo: refactor available (>>= to do)
def bindDemo :=
  Option.some 1 >>= fun x => Option.some (x + 1)

-- LetWildcard: should inform (redundant let _ ←)
example : IO Unit := do
  let _ ← IO.println "hello"
  pure ()

-- TupleMatch: should warn (match on tuple discriminant)
def addPair (x y : Nat) : Nat :=
  match (x, y) with
  | (a, b) => a + b

-- MatchToIfLet: should inform (two-arm match with wildcard)
def fromOption (x : Option Nat) : Nat :=
  match x with
  | some v => v
  | _ => 0

-- GetSet: should warn (get/set → modify)
private structure DemoState where
  count : Nat

def increment : StateM DemoState Unit := do
  let s ← get
  set { s with count := s.count + 1 }

-- InlineAllConst: refactor available (inline all usages of add1 from definition site)
example : Nat :=
  add1 3 + add1 5

-- ElsePureUnit: should inform (redundant else pure ())
example : IO Unit := do
  if true then
    IO.println "done"
  else
    pure ()

#heronProfile
