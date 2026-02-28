# Heron

**Refactoring and lint framework for [Lean 4](https://github.com/leanprover/lean4).**

Watches over _consistency and maintainability_ of large Lean projects by providing two kinds of rules:

- **Checks** — visible diagnostics (info, warning, or error) that underline problematic code and offer quick-fixes. May include detailed explanation and official documentation reference link.
- **Refactors** — code actions that appear when you open the refactor menu on a selection.

Both can carry additional metadata such as a category and official references:

![](./screenshots/popup.png)

## Usage

Add an import of Heron and enable all rules:

```lean
import Heron.Rules
set_option linter.heron true
```

### Checks

Checks show up automatically as underlined diagnostics. Hover to see the explanation, click the light-bulb to apply the suggested fix. See [`Heron/Check/`](./Heron/Check) for all available checks.

### Refactors

Refactors are invisible until you explicitly request them via the code action menu on a selection. See [`Heron/Refactor/`](./Heron/Refactor) for all available refactors.

### Disabling a rule

```lean
set_option linter.testIntros false
```

## Development

### Adding new rules

Check rules live in [`Heron/Check/`](./Heron/Check), refactor rules in [`Heron/Refactor/`](./Heron/Refactor). Each rule file contains:

- A match data struct describing what was detected
- A `detect` function that scans user source code
- A set of `replacements` to fix a single match
- Inline tests for false positives, replacements, and negatives

### Testing

Tests use compile-time assertion commands that show failures in-place:

```lean
#assertCheck testIntros `(tactic| intro a; intro b) => `(tactic| intro a b) in
example : Nat → Nat → True := by intro a; intro b; exact trivial

#assertRefactor inline `(term| myConst) => `(term| (42)) in
example : Nat := myConst

#assertIgnore testRfl in
example (a : Nat) : a = a + 0 := by simp
```

## Installation

At the moment of writing, you need to use a patched Lean (for now): [`github:wvhulle/lean4`](https://github.com/wvhulle/lean4).

- For Nix users: Configure your Nix flake to use the patched Lean. You will need to add the repo as input to your flake and then reference the `lean` or `lake` package exported by it.
- For other users:
  1. Clone the patched Lean into `../lean4`
  2. Build with `cmake` as documented in its `README.md`
  3. Add `lake` to your path:
     ```bash
     export PATH="$PWD/../lean4/build/release/stage1/bin:$PATH"
     ```

Then add the Lake dependency:

```toml
[[require]]
name = "heron"
git = "https://codeberg.org/wvhulle/heron"
rev = "main"
```

![Heron](./heron.jpg)

_Named after the [Heron](https://en.wikipedia.org/wiki/Heron) bird that watches over lakes since `lake` (in turn named after "Lean make") is the name of the build tool for Lean._
