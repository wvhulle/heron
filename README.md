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

### Pick the right version

Heron hooks into the Lean compiler, so it must be built with **exactly** the Lean version your
project uses. Use the ref that matches your `lean-toolchain`:

| Your `lean-toolchain` | Heron ref |
| --- | --- |
| `leanprover/lean4:v4.35.0` | `main` |
| `leanprover/lean4:v4.31.0` | `lean/v4.31.0` |
| `leanprover/lean4:v4.30.0` | `lean/v4.30.0` |
| `leanprover/lean4:v4.29.1` | `lean/v4.29.1` |
| [wvhulle/lean4](https://github.com/wvhulle/lean4) fork | `lean-fork/v4.31.0` |

The `lean-fork/v4.31.0` branch adds features that need the fork: hover popups, related-information labels
and import-analysis checks.

The repository is mirrored to GitHub (`https://github.com/wvhulle/heron`), so either URL works
below.

### Whole project, no imports (recommended)

Load Heron as a `lean --plugin`, so its linter runs on **every** module your package compiles and
no source file has to `import Heron`. In the consumer's `lakefile.lean`:

```lean
require heron from git "https://github.com/wvhulle/heron" @ "main"

package «your_pkg» where
  leanOptions := #[⟨`linter.heron, true⟩]
  plugins := #[`@heron/plugin]
  lintDriver := "heron/heron"
```

- `plugins` makes Lake build Heron's shared library on any platform and load it for every module.
  There is nothing to bootstrap, and updating Heron rebuilds it.
- `leanOptions` turns all rules on. Individual rules are switched off with
  ``⟨`linter.<rule>, false⟩`` or `set_option linter.<rule> false` in a file.
- `lintDriver` makes `lake lint` Heron's report command (next section).

A plain `lake build` then prints Heron's diagnostics for every module, and the editor shows them
with quick-fixes.

`lakefile.toml` cannot refer to a dependency's targets. For TOML projects, either convert to
`lakefile.lean` (`lake translate-config lean`) or use the per-file setup.

### Per-file (editor / LSP)

Add the dependency, in `lakefile.toml`:

```toml
[[require]]
name = "heron"
git = "https://github.com/wvhulle/heron"
rev = "main"
```

Then import Heron and enable its rules in the files you want linted:

```lean
import Heron
set_option linter.heron true
```

### Without touching your project (Nix)

The flake packages `heron-scan` with the toolchain from Heron's `lean-toolchain` (via
[lean4-nix](https://github.com/lenianiva/lean4-nix)) and runs it inside your project's
`lake env`. Build your project first, then run the Heron ref that matches your toolchain:

```sh
lake build
nix run github:wvhulle/heron/lean/v4.31.0 -- Consumer       # lint a library / directory
nix run github:wvhulle/heron/lean/v4.31.0 -- --fix Foo.lean  # apply fixes
```

This needs no `require`, no plugin and no `import`. It re-elaborates the files itself, though,
so it is slower than the plugin setup on large projects. The flake follows lean4-nix, which
lags a little behind Lean releases. A ref whose toolchain lean4-nix doesn't package yet fails to
evaluate with `attribute '"vX.Y.Z"' missing`.

## Reporting fixes from the command line (CI, scripts, batch fixing)

With the plugin setup above, `lake lint` builds your libraries and prints every fix in a
cargo/clippy-style report. Lake's incremental build is the cache, so only changed modules are
re-elaborated. Arguments after `--` go to the reporter:

```sh
lake lint                            # report all fixes across the workspace's libraries
lake lint -- Sparkle.Analog          # restrict to lake targets
lake lint -- --json | jq             # machine-readable
lake lint -- --fix                   # rewrite files in place
```

Heron also ships executables, which run in any project that requires Heron through
`lake exe …`:

| Command | What it does |
| --- | --- |
| `lake exe heron` | What `lake lint` runs. Builds your targets with Heron loaded as a plugin, then prints the fixes. |
| `lake exe heron-scan` | Self-contained. Imports the dependency closure once and elaborates the targets itself (own incremental cache + parallelism). Needs no plugin wiring; also reads from stdin (`-`). |

Common flags (both): `--json` (machine-readable), `--fix`/`--apply` (rewrite files in place),
`--color`/`--no-color`. `heron` adds `--no-build` (read an existing sink); `heron-scan` adds
`--per-file`, `--no-cache`, `--no-parallel`.

```sh
lake exe heron-scan --fix Foo/Bar.lean   # apply fixes to specific files
echo 'def f := fun x => x + 1' | lake exe heron-scan -   # lint from stdin
```

## Contributing

See [CONTRIBUTING.md](./CONTRIBUTING.md) for adding rules, testing and inspecting syntax trees.

## Name

![Heron](./heron.jpg)

_Named after the [Heron](https://en.wikipedia.org/wiki/Heron) bird that watches over lakes since `lake` (in turn named after "Lean make") is the name of the build tool for Lean._
