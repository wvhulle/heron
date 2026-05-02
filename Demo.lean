import Heron
-- The three modules below are imported but nothing from them is referenced —
-- they should each be flagged as unused.
import Lean.Data.Json.Parser
import Init.System.FilePath
import Lean.Data.Lsp.Capabilities

set_option linter.heron true
set_option heron.profile true

section Inlining
-- Definitions stay next to their usages so both the per-use-site refactor and
-- the def-site bulk refactor are visible without scrolling.

def greeting :=
  "hello"

example : String :=
  greeting

def add1 (n : Nat) :=
  n + 1

example : Nat :=
  add1 7

example : Nat :=
  add1 3 +
    add1 5

end Inlining

section RflProof

example (n : Nat) : n = n := by rfl

end RflProof

section TacticIntros

example : Nat → Nat → Nat → True := by
  intro a
  intro b
  intro c
  exact trivial

end TacticIntros

section FunctionBinders

def addNats (x : Nat) (y : Nat) :=
  x + y

end FunctionBinders

section MonadicIfNot

example : IO Unit := do
  if !true then
    IO.println
      "hello"

end MonadicIfNot

section TrivialIdRun

example : Nat :=
  Id.run
    (do
      return 42)

end TrivialIdRun

section MutableLocals

example : Nat :=
  Id.run
    (do
      let mut x := 5
      return x + 1)

-- Counterexample: legitimate imperative `mut`, no warning.
example : Nat :=
  Id.run
    (do
      let mut x := 0
      for _ in [1, 2, 3]do
        x := x + 1
      return x)

end MutableLocals

section BooleanMatch

def boolToNat (b : Bool) : Nat :=
  match b with
  | true => 1
  | false =>
    0

end BooleanMatch

section MatchArmsWithSharedBody
-- Edge case: only the consecutive pair sharing a body (`1 => 0`, `2 => 0`) is
-- merged; the wildcard arm has a different body and is left alone.

def mergeArmsDemo (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 0
  | 2 => 0
  | _ =>
    99

end MatchArmsWithSharedBody

section OptionMatch

def fromOption (x : Option Nat) : Nat :=
  match x with
  | some v => v
  | _ =>
    0

end OptionMatch

section TupleDiscriminant

def addPair (x y : Nat) : Nat :=
  match (x, y) with
  | (a, b) => a + b

end TupleDiscriminant

section MonadicBind

def bindDemo :=
  Option.some 1 >>= fun x =>
    Option.some
      (x + 1)

end MonadicBind

section LetWildcardArrow

example : IO Unit := do
  let _ ← IO.println "hello"
  pure
      ()

end LetWildcardArrow

section IfElsePure

example : IO Unit := do
  if true then
    IO.println "done"
  else
    pure
        ()

end IfElsePure

section StateGetSet

private structure DemoState where
  count : Nat

def increment : StateM DemoState Unit := do
  let s ← get
  set
      { s with count := s.count + 1 }

end StateGetSet

#heronProfile
