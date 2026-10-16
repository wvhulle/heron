# Heron

**Heron finds non-idiomatic [Lean 4](https://github.com/leanprover/lean4) code and fixes it: in your editor, on `lake build`, and in CI.**

```lean
example : Nat → Nat → True := by intro a; intro b; exact trivial
--                               ^^^^^^^^^^^^^^^^ Merge intros: replace with `intro a b`
```

![The `Id.run` check in the editor](./docs/images/editor-popup.png)

## Choose how to use Heron

| Setup | What you change in your project | What you get |
| --- | --- | --- |
| [Lakefile setup](docs/LakefileSetup.md) | three lines in `lakefile.lean` | editor hints and quick fixes, warnings on `lake build`, `lake lint` reports and fixes |
| [Per-file import](docs/PerFileImport.md) | a `require`, plus `import Heron` in each file to check | editor hints and quick fixes, warnings on `lake build`, for those files |
| [No project changes](docs/NoProjectChanges.md) | nothing | editor hints and quick fixes through `heron-language-server`; reports and fixes through `heron-scan` |

Most projects want the lakefile setup:

```lean
require heron from git "https://github.com/wvhulle/heron" @ "main"

package «your_pkg» where
  leanOptions := #[⟨`linter.heron, true⟩]
  plugins := #[`@heron/plugin]
  lintDriver := "heron/heron"
```

See [Rules](docs/Rules.md) for every check and refactor and how to turn them off.

## Supported Lean versions

Heron runs inside the Lean compiler, so it must be built with exactly your project's Lean
version. Use the ref that matches your `lean-toolchain`:

| Your `lean-toolchain` | Heron ref |
| --- | --- |
| `leanprover/lean4:v4.35.0` | `main` |
| `leanprover/lean4:v4.33.0` | `lean/v4.33.0` |
| `leanprover/lean4:v4.31.0` | `lean/v4.31.0` |
| `leanprover/lean4:v4.30.0` | `lean/v4.30.0` |
| `leanprover/lean4:v4.29.1` | `lean/v4.29.1` |
| [wvhulle/lean4](https://github.com/wvhulle/lean4) fork | `lean-fork/v4.31.0` |

The `lean-fork/v4.31.0` branch adds features that need the fork: hover popups with the full
explanation, related-information labels, and import-analysis checks. The repository is mirrored to
GitHub, so `https://codeberg.org/wvhulle/heron` works as well.

## Contributing

See [CONTRIBUTING.md](./CONTRIBUTING.md) for the repository layout, adding rules, testing and the
developer tools.

## Name

![Heron](./docs/images/heron.jpg)

_Named after the [Heron](https://en.wikipedia.org/wiki/Heron) bird that watches over lakes since `lake` (in turn named after "Lean make") is the name of the build tool for Lean._
