# Per-file import

Require Heron and enable it only in the files you want checked. This also works with
`lakefile.toml`, but `lake lint` is not available.

```toml
[[require]]
name = "heron"
git = "https://github.com/wvhulle/heron"
rev = "main"
```

Use the `rev` that matches your `lean-toolchain` (see
[Supported Lean versions](../README.md#supported-lean-versions)). Then, in each file:

```lean
import Heron
set_option linter.heron true
```

Those files get Heron's warnings on `lake build` and its quick fixes and refactors in the editor.
