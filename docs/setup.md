# Setup

| Setup | What you change in your project | What you get |
| --- | --- | --- |
| [Lakefile setup](#lakefile-setup) | three lines in `lakefile.lean` | editor hints and quick fixes, warnings on `lake build`, `lake lint` reports and fixes |
| [Per-file import](#per-file-import) | a `require`, plus `import Heron` in each file to check | editor hints and quick fixes, warnings on `lake build`, for those files |
| [No project changes](#no-project-changes) | nothing | editor hints and quick fixes through `heron serve`; reports and fixes through `heron scan` |

Most projects want the lakefile setup. Every setup needs the Heron ref that matches your
`lean-toolchain`, listed under [Supported Lean versions](#supported-lean-versions).

## Lakefile setup

Load Heron as a plugin from your project's `lakefile.lean`. Every module is checked, in the editor
and on `lake build`, without any `import Heron`, and `lake lint` reports all fixes.

In your project's `lakefile.lean`, require Heron and load its plugin:

```lean
require heron from git "https://github.com/wvhulle/heron" @ "main"

package «your_pkg» where
  leanOptions := #[⟨`linter.heron, true⟩]
  plugins := #[`@heron/plugin]
  lintDriver := "heron/heron"
  lintDriverArgs := #["lint"]
```

`lakefile.toml` cannot refer to a dependency's targets. Convert it with
`lake translate-config lean`, or use the [per-file import](#per-file-import) instead.

### What you get

- **In the editor:** checks underline code and offer a quick fix on the light bulb. Refactors
  appear in the code-action menu when you select code.
- **On `lake build`:** every check is reported as a warning.
- **With `lake lint`:** a cargo/clippy-style report of all fixes. Lake's incremental build is the
  cache, so only changed modules are re-checked.

```sh
lake lint                    # report fixes across the workspace's libraries
lake lint -- Sparkle.Analog  # restrict to lake targets
lake lint -- --json | jq     # machine-readable
lake lint -- --fix           # rewrite files in place
```

`lake lint` runs `heron lint`, which you can also call as `lake exe heron lint`. It builds your
targets with the plugin, then prints the fixes. It accepts `--json`, `--fix`, `--apply`, `--color`
and `--no-color`, and `--no-build` to read the last build's results.

[Rules](rules.md) explains how to list the rules and turn single ones off.

## Per-file import

Require Heron and enable it only in the files you want checked. This also works with
`lakefile.toml`, but `lake lint` is not available.

```toml
[[require]]
name = "heron"
git = "https://github.com/wvhulle/heron"
rev = "main"
```

Then, in each file:

```lean
import Heron
set_option linter.heron true
```

Those files get Heron's warnings on `lake build` and its quick fixes and refactors in the editor.

## No project changes

Two subcommands of `heron` run Heron on a Lean project that has never heard of it: `heron serve`
in your editor and `heron scan` on the command line. Neither needs a `require`, plugin or `import`.

### In the editor: `heron serve`

`heron serve` is a second Lean language server that runs next to your normal one and shows only
Heron's hints, quick fixes and refactors. See [Editor setup](editor.md) to add it to Helix, Neovim
or VS Code, and [Install](install.md) to get the `heron` binary.

### On the command line: `heron scan`

Build your project, then run `heron scan` in its root directory with a `heron` binary
[installed](install.md) from the Heron ref that matches your toolchain. It runs
`lake env lean --plugin=<Heron plugin>` on each file, the way `lake build` does in a project with
the lakefile setup, so it reports the same fixes.

```sh
lake build
heron scan Consumer        # check a library or directory
heron scan --fix Foo.lean  # apply fixes
```

A project that requires Heron can also run it as `lake exe heron scan`:

```sh
lake exe heron scan --fix Foo/Bar.lean
echo 'def f := fun x => x + 1' | lake exe heron scan -
```

It accepts `--json`, `--fix`, `--apply`, `--all`, `--color` and `--no-color`, and reads stdin
with `-`. `--rule <names>` runs only the named checks, separated by commas. `--jobs <n>` sets how many files
are checked at the same time; by default it is the number of CPUs, at most one per 2 GB of
available memory (4 where `/proc` does not tell). `--memory <megabytes>` (default 8192) is the
memory limit of each Lean process, so one file that runs away is stopped instead of the machine. When two fixes overlap, `--fix` and `--apply` apply the first and skip the other;
run them again to apply it. `heron rules` lists every check and refactor with its description and
sources; with `--json` it prints them as a JSON array. A check that flags code without a fix
is reported like any other finding; in `--json` output such a finding has no `after` field.

#### With Nix

Without installing anything, run the same commands through the flake:

```sh
nix run github:wvhulle/heron/main -- scan Consumer
nix run github:wvhulle/heron/main -- scan --fix Foo.lean
```

## Supported Lean versions

Heron runs inside the Lean compiler, so it must be built with exactly your project's Lean
version. Use the ref that matches your `lean-toolchain`. `main` always points at the same commit
as the branch of the newest Lean release:

| Your `lean-toolchain` | Heron ref |
| --- | --- |
| `leanprover/lean4:v4.35.0` | `lean/v4.35.0` or `main` |
| `leanprover/lean4:v4.34.1` | `lean/v4.34.1` |
| `leanprover/lean4:v4.34.0` | `lean/v4.34.0` |
| `leanprover/lean4:v4.33.1` | `lean/v4.33.1` |
| `leanprover/lean4:v4.33.0` | `lean/v4.33.0` |
| `leanprover/lean4:v4.32.2` | `lean/v4.32.2` |
| `leanprover/lean4:v4.32.0` | `lean/v4.32.0` |
| `leanprover/lean4:v4.31.0` | `lean/v4.31.0` |
| `leanprover/lean4:v4.30.0` | `lean/v4.30.0` |
| `leanprover/lean4:v4.29.1` | `lean/v4.29.1` |
| [wvhulle/lean4](https://github.com/wvhulle/lean4) fork | `lean-fork/v4.31.0` |

The `lean-fork/v4.31.0` branch adds hover popups with the full explanation, related-information
labels and import-analysis checks, which need the fork. `https://codeberg.org/wvhulle/heron` works
as well as the GitHub mirror.
