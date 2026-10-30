# Editor setup

`heron serve` is a second Lean language server that runs next to your normal one, in any Lake
project, without changes to the project. It starts its own `lake serve` with Heron loaded as a
plugin and passes on only Heron's warnings, quick fixes and refactors, so your normal Lean server
stays untouched. Each open file is elaborated twice, once per server, which costs extra CPU and
memory on large projects.

Projects that use the [lakefile setup](setup.md#lakefile-setup) or the
[per-file import](setup.md#per-file-import) already get Heron through their normal Lean server and
need none of this.

Every editor below runs the command `heron serve`, so [install](install.md) `heron` first. If it
is not on your editor's `PATH`, replace `heron` by the full path to the binary. With Nix, see
[With Nix](#with-nix) for the command to use instead.

## Helix

In `languages.toml`:

```toml
[language-server.heron]
command = "heron"
args = ["serve"]

[[language]]
name = "lean"
language-servers = ["lean4_lsp", "heron"]
```

## Neovim

Neovim 0.11 and newer attach several servers to one buffer. Add to your `init.lua`:

```lua
vim.lsp.config('heron', {
  cmd = { 'heron', 'serve' },
  filetypes = { 'lean' },
  root_markers = { 'lakefile.lean', 'lakefile.toml', 'lean-toolchain' },
})
vim.lsp.enable('heron')
```

This works next to [lean.nvim](https://github.com/Julian/lean.nvim), which keeps running its own
Lean server.

## VS Code

The [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4) runs
one server and cannot add a second. Install a generic LSP client next to it, such as
[Generic LSP Client](https://marketplace.visualstudio.com/items?itemName=zsol.vscode-glspc), and
configure it in `settings.json`:

```json
{
  "glspc.server.command": "heron",
  "glspc.server.commandArguments": ["serve"],
  "glspc.server.languageId": ["lean4"]
}
```

The extension registers one server, so it cannot serve another language at the same time. When VS
Code reports `spawn heron ENOENT`, it does not see `heron` on its `PATH`: give the full path to the
binary, or start VS Code from a shell where `heron` resolves.

## With Nix

This section only applies if you use Nix. Instead of an installed `heron`, an editor can run the
flake directly with the command `nix` and the arguments `run github:wvhulle/heron -- serve`. In
Helix:

```toml
[language-server.heron]
command = "nix"
args = ["run", "github:wvhulle/heron", "--", "serve"]
```

In a Nix-managed editor configuration, use the package from a flake input `heron`:
`"${heron.packages.x86_64-linux.heron}/bin/heron"`.

## Progress and idle states

The server runs `lean --version` in the project and loads the plugin built for that Lean version.

A binary [built from source](install.md#from-source) clones the `lean/v<version>` branch into
`~/.cache/heron/<version>` (or `$HERON_CACHE_DIR`) and builds the plugin there on first use. That
takes a few minutes, which the editor shows as LSP progress (in Helix, the spinner and
`[built/total]` message in the statusline); the full build log goes to the language-server log.

The [Nix package](install.md#nix) ships a plugin for every stock Lean version in the
[Supported Lean versions](setup.md#supported-lean-versions) table and never builds at run time:
for any other version it stays idle and lists the versions it bundles.

The server also stays idle when Heron has no branch for the project's Lean version or the build
fails, and shows the reason as an editor message. When the project's `lakefile` already lists
`@heron/plugin`, it stays idle with only a line in the log. It remembers a version it could not
serve and only tries again once Heron's branches change, so an unsupported project costs one
quick `git ls-remote` per start.

Like the lakefile setup, the linter writes `.lake/build/heron-fixes/` in each project you open.

`heron serve` is built on [Weir](https://codeberg.org/wvhulle/weir), a proxy in front of
`lake serve` that other Lean plugins can reuse.
