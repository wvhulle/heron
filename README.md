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

Add the Lake dependency:

```toml
[[require]]
name = "heron"
git = "https://codeberg.org/wvhulle/heron"
rev = "main"
```

You then have two ways to surface Heron's diagnostics in your project.

### Per-file (editor / LSP)

Import Heron and enable its rules in the files you want linted:

```lean
import Heron
set_option linter.heron true
```

### Whole project, no imports (recommended)

Load Heron as a `lean --plugin` so its linter runs on **every** module your build compiles — no
`import Heron` in any source file. Heron's `Heron` library defaults to the `shared` facet, so its
plugin shared library is emitted as part of a normal build. Wire it up once in the consumer's
`lakefile.lean`:

```lean
package «your_pkg» where
  -- enable the rules everywhere (`weak.` = no-op if the plugin is absent)
  leanOptions := #[⟨`weak.linter.heron, true⟩]
  -- load Heron for every compiled module; `weakLeanArgs` keeps the path out of the build trace
  weakLeanArgs := #["--plugin", ".lake/packages/heron/.lake/build/lib/libheron_Heron.so"]

require heron from git "https://codeberg.org/wvhulle/heron" @ "main"
```

Bootstrap (or refresh, after updating Heron) the plugin library with:

```sh
lake build heron/Heron:shared
```

After that, a plain `lake build` reports Heron's fixes inline on every module.

## Headless reporters (CI, scripts, batch fixing)

Heron ships two executables that surface fixes outside the editor. Because Lake exposes a
dependency's executables by name, you can run them from **any project that requires Heron** with
`lake exe …` — no extra wiring:

| Command | What it does |
| --- | --- |
| `lake exe heron` | Build-integrated (clippy model). Builds your targets with Heron loaded as a plugin, then prints the fixes. Builds the plugin `.so` itself if missing. Rides Lake's incremental cache. |
| `lake exe heron-scan` | Self-contained. Imports the dependency closure once and elaborates the targets itself (own incremental cache + parallelism). Needs no lakefile changes; also reads from stdin (`-`). |

Common flags (both): `--json` (machine-readable), `--fix`/`--apply` (rewrite files in place),
`--color`/`--no-color`. `heron` adds `--no-build` (read an existing sink); `heron-scan` adds
`--per-file`, `--no-cache`, `--no-parallel`.

```sh
lake exe heron                       # report all fixes across the workspace's libraries
lake exe heron Sparkle.Analog        # restrict to lake targets
lake exe heron --json | jq           # machine-readable
lake exe heron-scan --fix Foo/Bar.lean   # apply fixes to specific files
echo 'def f := fun x => x + 1' | lake exe heron-scan -   # lint from stdin
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
