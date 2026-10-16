# No project changes

Two tools run Heron on a Lean project that has never heard of it: `heron-language-server` in your
editor and `heron-scan` on the command line. Neither needs a `require`, plugin or `import`.

## In the editor: `heron-language-server`

`heron-language-server` is a second Lean language server that runs next to your normal one. It
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

With other editor setups, add `heron-language-server` as an extra Lean language server, for
example in Helix:

```toml
# languages.toml
[language-server.heron]
command = "nix"
args = ["run", "github:wvhulle/heron#heron-language-server"]

[[language]]
name = "lean"
language-servers = ["lean4_lsp", "heron"]
```

Without Nix, build it from the branch that matches your toolchain and point your editor at the
binary:

```sh
git clone --branch main https://github.com/wvhulle/heron && cd heron
lake build Heron:shared heron-language-server
# editor command: <checkout>/.lake/build/bin/heron-language-server
```

### Lean versions and when the server stays idle

The server runs `lean --version` in the project and loads the plugin built for that Lean version.
For any version other than its own, it clones the matching Heron branch into
`~/.cache/heron/<version>` (or `$HERON_CACHE_DIR`) and builds the plugin there on first use. The
first start on a new version therefore takes a few minutes, and the build log appears in the
editor's language-server log.

The server stays idle, and says why in that log, when Heron has no branch for the project's Lean
version or when the project's `lakefile` already lists `@heron/plugin`.

Like the lakefile setup, the linter writes `.lake/build/heron-fixes/` in each project you open.

## On the command line: `heron-scan`

Build your project, then run `heron-scan` from the Heron ref that matches your toolchain. It
re-elaborates the files itself, so it is slower than the lakefile setup on large projects.

```sh
lake build
nix run github:wvhulle/heron/main -- Consumer        # check a library or directory
nix run github:wvhulle/heron/main -- --fix Foo.lean  # apply fixes
```

A project that requires Heron can also run it as `lake exe heron-scan`:

```sh
lake exe heron-scan --fix Foo/Bar.lean
echo 'def f := fun x => x + 1' | lake exe heron-scan -
```

It accepts `--json`, `--fix`, `--apply`, `--color` and `--no-color`, plus `--per-file`,
`--no-cache` and `--no-parallel`, and reads stdin with `-`.
