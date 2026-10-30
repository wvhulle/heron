# Install

The `heron` binary runs `heron serve` in your editor and `heron scan`, `heron lint` and
`heron rules` on the command line. The [lakefile setup](setup.md#lakefile-setup) and the
[per-file import](setup.md#per-file-import) do not need it: Lake builds Heron as a dependency of
your project and runs it as `lake exe heron`.

There are no prebuilt binaries to download. Use the Nix package, whose builds are cached, or build
from source.

## Nix

Run it straight from the flake:

```sh
nix run github:wvhulle/heron -- rules
nix run github:wvhulle/heron -- scan MyLibrary
```

Or install it into your profile:

```sh
nix profile install github:wvhulle/heron
heron --help
```

In a flake of your own, add `heron.url = "github:wvhulle/heron";` to the inputs and use
`heron.packages.x86_64-linux.heron`, for example as the command of an [editor](editor.md)
configuration: `"${heron.packages.x86_64-linux.heron}/bin/heron"`.

The flake's `nixConfig` adds the substituter `wvhulle.cachix.org`, so Nix downloads the build
instead of compiling Lean and Heron; accept it when Nix asks, or add it to your own `nix.conf`.

The package includes the plugin for every stock Lean version in the
[Supported Lean versions](../README.md#supported-lean-versions) table and never builds anything
at run time. For a project on any other Lean version, `heron serve` stays idle and lists the
versions it includes.

## Ubuntu

Install `git`, `curl` and a C toolchain, then the Lean version manager
[elan](https://github.com/leanprover/elan):

```sh
sudo apt install git curl build-essential
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Clone the Heron ref that matches your project's `lean-toolchain` and build the binary and the
plugin. elan installs the Lean version that the checkout's `lean-toolchain` names:

```sh
git clone --branch main https://github.com/wvhulle/heron && cd heron
lake build heron plugin
```

The binary is `.lake/build/bin/heron`. Put it on your `PATH` or point your editor at it.

A binary built from source serves every Lean version that has a `lean/v<version>` branch. When it
opens a project on another version than its own, it clones that branch into
`~/.cache/heron/<version>` (or `$HERON_CACHE_DIR`) and builds the plugin there. The first build
takes a few minutes and is shown as [editor progress](editor.md#progress-and-idle-states).

## Development shells

To work on Heron itself, `nix develop` gives elan (`unmanaged-vanilla`, the default) and
`nix develop .#managed-stock` gives the Nix-built Lean. See [Style](style.md).
