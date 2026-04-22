# Heron

**Refactoring and lint framework for [Lean 4](https://github.com/leanprover/lean4).**

Watches over _consistency and maintainability_ of large Lean projects by providing two kinds of rules:

- **Checks** — visible diagnostics that underline problematic code and offer quick-fixes.
- **Refactors** — code actions that appear when you open the refactor menu on a selection.

The `Id.run` check in action.

![](./screenshots/popup.png)

## Usage

Add an import and enable all rules:

```lean
import Heron
set_option linter.heron true
```

See [`Heron/Check/`](./Heron/Check) for all available checks and [`Heron/Refactor/`](./Heron/Refactor) for refactors.

### DeadHeron

Import analysis rules (unused imports, unnecessary `public`/`meta` qualifiers) require a [patched Lean fork](https://github.com/wvhulle/lean4). Import them separately:

```lean
import DeadHeron
```

### Checks

Checks show up automatically as underlined diagnostics around anti-patterns.

- Move your cursor to the underline to see a short message.
- Enable inline diagnostics in your editor settings to see inline labels.
- Click the light-bulb to apply the suggested fix.
- Hover to open a popup with detailed explanation.
- Checks for unused patterns are shown dimmed; deprecated patterns with strike-through.

### Refactors

Refactors are invisible until you explicitly request them via the code action menu on a selection. They are intended for offering an easy way to users to rewrite between equally acceptable styles. Use checks for showing a clear diagnostic to the user that indicates a piece of code that represents an anti-pattern.

### Disabling a Rule

```lean
set_option linter.mergeIntros false
```

## Installation

The core `Heron` library works with standard Lean 4. `DeadHeron` (import analysis rules) requires the [patched Lean fork](https://github.com/wvhulle/lean4).

Add the Lake dependency:

```toml
[[require]]
name = "heron"
git = "https://codeberg.org/wvhulle/heron"
rev = "main"
```

## Development

![Heron](./heron.jpg)

_Named after the [Heron](https://en.wikipedia.org/wiki/Heron) bird that watches over lakes since `lake` (in turn named after "Lean make") is the name of the build tool for Lean._

### Adding New Rules

Check rules live in [`Heron/Check/`](./Heron/Check), refactor rules in [`Heron/Refactor/`](./Heron/Refactor). Each rule file contains:

- A match data struct describing what was detected
- A `detect` function that scans user source code
- A set of `replacements` to fix a single match
- Inline tests for false positives, replacements, and negatives

### Testing

Tests use compile-time assertion commands that verify rules at build time. Failures appear as errors in the build output.

`#assertCheck` verifies that a check rule transforms a command into the expected result:

```lean
#assertCheck mergeIntros in
example : Nat → Nat → True := by intro a; intro b; exact trivial
becomes `(example : Nat → Nat → True := by intro a b; exact trivial)
```

`#assertRefactor` does the same for refactor rules:

```lean
#assertRefactor inline in
example : Nat := myConst
becomes `(example : Nat := (42))
```

`#assertIgnore` verifies that a rule produces no edits for the given command:

```lean
#assertIgnore rflToExactRfl in
example (a : Nat) : a = a + 0 := by simp
```
