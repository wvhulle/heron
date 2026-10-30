# Setup

Three ways to use Heron, from most to least integrated. Each needs the Heron ref that matches your
`lean-toolchain` (see [Supported Lean versions](../README.md#supported-lean-versions)).

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

Turn single rules off as described under [Rules](../README.md#rules) in the README; `lake exe
heron rules` lists them.

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

`heron serve` is a second Lean language server that runs next to your normal one. It
starts its own `lake serve` with Heron loaded as a plugin and passes on only Heron's warnings,
quick fixes and refactors, so your normal Lean server stays untouched. Each open file is
elaborated twice, once per server, which costs extra CPU and memory on large projects.

Add `heron serve` as an extra Lean language server, for example in Helix:

```toml
# languages.toml
[language-server.heron]
command = "nix"
args = ["run", "github:wvhulle/heron", "--", "serve"]

[[language]]
name = "lean"
language-servers = ["lean4_lsp", "heron"]
```

Without Nix, build it from the branch that matches your toolchain and point your editor at the
binary:

```sh
git clone --branch main https://github.com/wvhulle/heron && cd heron
lake build plugin heron
# editor command: <checkout>/.lake/build/bin/heron serve
```

#### Lean versions and when the server stays idle

The server runs `lean --version` in the project and loads the plugin built for that Lean version.
The Nix package ships a plugin for every stock Lean version in the README's table and never builds
at run time: for any other version it stays idle and lists the versions it bundles. A binary built
from source instead clones the `lean/v<version>` branch into `~/.cache/heron/<version>` (or
`$HERON_CACHE_DIR`) and builds the plugin there on first use. That takes a few minutes, which the editor shows as LSP progress (in Helix, the
spinner and `[built/total]` message in the statusline); the full build log goes to the
language-server log.

The server also stays idle when Heron has no branch for the project's Lean version or the build fails,
and shows the reason as an editor message. When the project's `lakefile` already lists
`@heron/plugin`, it stays idle with only a line in the log. It remembers a version it could not
serve and only tries again once Heron's branches change, so an unsupported project costs one
quick `git ls-remote` per start.

`heron serve` is built on [Weir](https://codeberg.org/wvhulle/weir), a proxy in front of `lake
serve` that other Lean plugins can reuse.

Like the lakefile setup, the linter writes `.lake/build/heron-fixes/` in each project you open.

### On the command line: `heron scan`

Build your project, then run `heron scan` in its root directory, from the Heron ref that matches
your toolchain. It runs `lake env lean --plugin=<Heron plugin>` on each file, the way `lake build`
does in a project with the lakefile setup, so it reports the same fixes.

```sh
lake build
nix run github:wvhulle/heron/main -- scan Consumer        # check a library or directory
nix run github:wvhulle/heron/main -- scan --fix Foo.lean  # apply fixes
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
