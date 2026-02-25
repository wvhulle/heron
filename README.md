# Heron

**Refactoring and lint framework for [Lean 4](https://github.com/leanprover/lean4).**

The intention of this project is to watch over _consistency and maintainability_ of large Lean projects.

![Heron](./heron.jpg)

_Named after the [Heron](https://en.wikipedia.org/wiki/Heron) bird that watches over lakes since `lake` (in turn named after "Lean make") is the name of the build tool for Lean._

How does it work?

Each rule detects an anti-pattern or bug and suggests a fix that can be applied as an editor code action. Violations detected by rules may have info, warn or error level, or be lazy (invisible but triggered by explicit refactor).

## Installation

### 1. Patch Lean

Using your system's `elan` binary will likely (unfortunately) not work. You need to use a patched Lean (for now) from [`github:wvhulle/lean4`](https://github.com/wvhulle/lean4)

- For Nix users: Configure your Nix flake to use the patched Lean. You will need to add the repo as input to your flake and then reference the `lean` or `lake` package exported by it.
- For other users: You need to:
  1. Clone the patched Lean into `../lean4`
  2. Build the patched Lean with `cmake` as documented in its `README.md` file.
  3. Add the `lake` to your path:
     ```bash
     export PATH="$PWD/../lean4/build/release/stage1/bin:$PATH"
     ```

_(Currently a fork of Lean is being used since not everything is ready in Lean for comprehensive linters, will try to be up-streamed in future. Since it is very time-intensive to create and review PRs, I am focusing currently on getting Heron ready for testing.)_

### 2. Add Heron Dependency

Add as a Lake dependency:

```toml
[[require]]
name = "heron"
git = "https://codeberg.org/wvhulle/heron"
rev = "main"
```

For reproducible builds, it is recommended to pin the rev to a commit hash.

To fetch to the latest Heron version (can be used later for updates):

```bash
lake update heron
```

As a check, try to pre-fetch and prebuild (done automatically when you load in the next steps):

```bash
lake build heron
```

## Usage

Add an import of Heron to the top of the Lean file you want to lint:

```lean
import Heron.Rules
```

_(Lean / Lake does not support separate linter binaries at the moment, so this small change in your user code is required for you to enjoy the features of this linter.)_

It is required to enable at least one rule. To enable all linters, you can use:

```lean
set_option linter.heron true
```

The following steps depend on your editor. This project should be supported by all major editors (if not, please report an issue).

VS Code:

- refactors: select code, open the refactor menu with `ctrl+shift+p`, type 'refactor'
- diagnostics: hover over code being underlined, click light-bulb, select fix

Helix:

- refactors: select code, press `space` then `a`, select refactor
- diagnostics: select violation code, press `space` then `a`, select fix

For example, when you put your cursor on `!a` and open the refactor menu:

```lean
example : String :=
  let a := false
  if !a then "No a" else "Yes a"
```

... you should see an option to invert the condition and switch the then and else branch.

If you have all linters enabled (which is the default), you might see multiple suggestions. This may be overwhelming and feel free to report issues related to this.

To disable a noisy one:

```lean
set_option linter.testIntros false
```

## Development

This project was inspired by the approach I took in [nu-lint](https://codeberg.org/wvhulle/nu-lint) and turned out to be very maintainable.

Currently not that many ready-to-use "rules" have been included, but the foundation for defining lints and refactors is stabilizing. The focus is now on extending the rule database with new rules. For new implementations, see existing [`Heron/Rules/`](./Heron/Rules).

Rules live in separate sub-files of `Heron/Rules/`, each with:

- A "fix data" struct: a type-safe description of what constitutes a violation / what is needed to fix
- Detection method for violations that scans user's Lean source code
- Set of replacements to fix a single violation
- Labels for each replacement (may be shown inline by supported editors)
- Tests for false positives, replacements, and negatives

Tests use compile-time (they should show real-time failed assertions in-place) assertion commands:

```lean
-- Assert a refactor rule produces specific replacements
#assertRefactor inline `(term| myConst) => `(term| (42)) in
example : Nat := myConst

-- Assert a diagnostic rule produces specific replacements
#assertFix testIntros `(tactic| intro a; intro b) => `(tactic| intro a b) in
example : Nat → Nat → True := by intro a; intro b; exact trivial

-- Assert a rule produces no replacements
#assertIgnore testRfl in
example (a : Nat) : a = a + 0 := by simp
```
