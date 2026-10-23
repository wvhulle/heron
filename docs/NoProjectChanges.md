# No project changes

Two subcommands of `heron` run Heron on a Lean project that has never heard of it: `heron serve`
in your editor and `heron scan` on the command line. Neither needs a `require`, plugin or `import`.

## In the editor: `heron serve`

`heron serve` is a second Lean language server that runs next to your normal one. It
starts its own `lake serve` with Heron loaded as a plugin and passes on only Heron's warnings,
quick fixes and refactors, so your normal Lean server stays untouched. Each open file is
elaborated twice, once per server, which costs extra CPU and memory on large projects.

With home-manager and the `services.toolchain.langs` module of
[hm-dev-tools](https://codeberg.org/wvhulle/hm-dev-tools), import this flake's module and enable
it. It adds a `heron` server to the Lean language:

```nix
home-manager.users.<you> = {
  imports = [ heron.homeModules.default ];
  programs.heron.enable = true;
};
```

With other editor setups, add `heron serve` as an extra Lean language server, for example in
Helix:

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

### Lean versions and when the server stays idle

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

## On the command line: `heron scan`

Build your project, then run `heron scan` in its root directory, from the Heron ref that matches
your toolchain. It re-elaborates the files itself, so it is slower than the lakefile setup on large
projects.

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

It accepts `--json`, `--fix`, `--apply`, `--color` and `--no-color`, plus `--per-file`,
`--no-cache` and `--no-parallel`, and reads stdin with `-`. `--rule <names>` runs only the named
checks, separated by commas. `heron rules` lists every check and refactor with its description and
sources; with `--json` it prints them as a JSON array. A check that flags code without a fix
is reported like any other finding; in `--json` output such a finding has no `after` field.
