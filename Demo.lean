import Heron.Rules.Rfl
import Heron.Rules.Intros
import Heron.Rules.Inline

/-!# Heron Demo

Open this file in VS Code (or another Lean editor) to see the diagnostics
and code-action fixes that Heron provides. Each section below triggers a
different linter rule. Hover over the yellow warnings, then click
"Quick Fix…" (or press `ctrl+.`) to apply the suggested rewrite.
-/

/-!## 1. `rfl` → `exact rfl`

Bare `rfl` in tactic mode can be replaced with the more explicit `exact rfl`.
-/

set_option linter.testRfl true

example (n : Nat) : n = n := by rfl

example (a b : Nat) (_ : a = b) : a = a := by rfl

/-!## 2. Sequential `intro` → combined `intro`

Consecutive `intro` tactics can be merged into a single `intro` with
multiple binders.
-/

set_option linter.testIntros true

example : Nat → Nat → Nat → True := by
  intro a
  intro b
  intro c
  exact trivial

/-!## 3. Inline definitions

Non-recursive definitions and let-bindings can be delta-reduced at the
call site.
-/

set_option linter.inline true

def greeting :=
  "hello"

def add1 (n : Nat) :=
  n + 1

example : String :=
  greeting

example : Nat :=
  add1 7
