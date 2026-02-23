# Heron

Linting rules with auto-fixes for [Lean 4](https://github.com/leanprover/lean4). Each rule detects a pattern and suggests a fix that can be applied as an editor code action.

Named after the bird that watches over lakes.

## Rules

| Rule | File | Detects | Suggests |
|------|------|---------|----------|
| `testRfl` | `Heron/Rules/Rfl.lean` | Bare `rfl` tactic | `exact rfl` |
| `testIntros` | `Heron/Rules/Intros.lean` | Sequential `intro` tactics | Combined `intro a b` |
| `inline` | `Heron/Rules/Inline.lean` | Inlineable const/let usage | Delta-expanded expression |

## Usage

Add as a Lake dependency:

```toml
[[require]]
name = "heron"
git = "..."
rev = "main"
```

Enable a rule with `set_option`:

```lean
set_option linter.testRfl true in
example : a = a := by rfl  -- warning: use `exact rfl`
```

## Development

Rules live in `Heron/Rules/`, each with typed fix data, detection, and co-located tests. Tests use compile-time assertion commands:

```lean
-- Assert a specific suggestion is produced
#assertSuggests testRfl `(tactic| rfl) => `(tactic| exact rfl) in
example (a : Nat) : a = a := by rfl

-- Assert specific edits are produced
#assertEdits testIntros `(tactic| intro a; intro b) => `(tactic| intro a b) in
example : Nat → Nat → True := by intro a; intro b; exact trivial

-- Assert no suggestions are produced
#assertNoSuggests testRfl in
example (a : Nat) : a = a + 0 := by simp
```
