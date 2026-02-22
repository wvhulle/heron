# Heron 

Collection of useful linting rules with auto-fixes for the Lean4 programming language.

The name is based on the Heron bird that watches over lakes, a nameplay on the `lake` build tool of lean.


## Rules

Inlining:

- Inline function at all call-sites and delete definition
- Inline function at current call-site



## Development

It is recommended to use the `assertSuggests` command shipped with tis project for writing tests.

It asserts at build time whether lints actually rewrite Lean syntax properly:

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
