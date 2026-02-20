# Assert-Suggests

A custom Lean command to write tests for linters.

Use it like this:

```lean
import AssertSuggests -- This library
import Test.Linters -- File with custom linter `testIntros` definition

#assertSuggests testIntros `(tactic| intro x
  intro y) => `(tactic| intro x y) in
example : ∀ x y : Nat, x = x := by
  intro x
  intro y
  rfl
```

This asserts that the linter named `testIntros` (including whitespace)

```lean
intro x
intro y
```

actually gets flattened into `intro x y`.
