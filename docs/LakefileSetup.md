# Lakefile setup

Load Heron as a plugin from your project's `lakefile.lean`. Every module is checked, in the editor
and on `lake build`, without any `import Heron`, and `lake lint` reports all fixes.

## Setup

In your project's `lakefile.lean`, require the Heron ref that matches your `lean-toolchain` (see
[Supported Lean versions](../README.md#supported-lean-versions)):

```lean
require heron from git "https://github.com/wvhulle/heron" @ "main"

package «your_pkg» where
  leanOptions := #[⟨`linter.heron, true⟩]
  plugins := #[`@heron/plugin]
  lintDriver := "heron/heron"
```

`lakefile.toml` cannot refer to a dependency's targets. Convert it with
`lake translate-config lean`, or use the [per-file import](PerFileImport.md) instead.

## What you get

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

`lake lint` runs Heron's `heron` executable, which you can also call as `lake exe heron`. It
builds your targets with the plugin, then prints the fixes. It accepts `--json`, `--fix`,
`--apply`, `--color` and `--no-color`, and `--no-build` to read the last build's results.

Turn single rules off as described under [Rules](../README.md#rules) in the README; `lake exe
heron-scan rules` lists them.
