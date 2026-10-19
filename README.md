# Heron

**Heron finds non-idiomatic [Lean 4](https://github.com/leanprover/lean4) code and fixes it: in your editor, on `lake build`, and in CI.**

```lean
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
--^^^^^ Match on the parameters directly with `def f : A → B | pattern => …`
  | .saturday | .sunday => true
  | _ => false
```

The quick fix turns it into

```lean
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false
```

Hovering the underline explains the rule: when a parameter is named only to be matched on
immediately, the cases can be written directly after the signature. Move the parameter's type to
the right of the colon, so the declared type becomes a function type, and replace `:= match … with`
by the alternatives. The popup links to the rule's source, here the
[Pattern-matching definitions](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#pattern-matching-definitions)
section of _Functional Programming in Lean_, and names the option that turns it off:
`set_option linter.matchOnParametersToPatternMatchingDefinition false`.

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

## Rules

Heron has two kinds of rules. **Checks** run on every command once `linter.heron` is on; each
underlines the code it flags and, for most checks, offers a quick fix. **Refactors** never flag
anything and appear in the editor's code-action menu when the cursor is on code they can rewrite.
Every rule names the book section, style guide or other linter it is based on.

`heron-scan rules` prints every rule with its description and sources, from any Lean project:

```sh
nix run github:wvhulle/heron/main -- rules   # or, in a project that requires Heron:
lake exe heron-scan rules
lake exe heron-scan rules --json              # machine-readable
```

Turn a rule off with `set_option linter.<rule> false` in a file, or ``⟨`linter.<rule>, false⟩``
in `leanOptions`.

## Supported Lean versions

Heron runs inside the Lean compiler, so it must be built with exactly your project's Lean
version. Use the ref that matches your `lean-toolchain`:

| Your `lean-toolchain` | Heron ref |
| --- | --- |
| `leanprover/lean4:v4.35.0` | `main` |
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

The `lean-fork/v4.31.0` branch adds features that need the fork: hover popups with the full
explanation, related-information labels, and import-analysis checks. The repository is mirrored to
GitHub, so `https://codeberg.org/wvhulle/heron` works as well.

## Contributing

See [CONTRIBUTING.md](./CONTRIBUTING.md) for the repository layout, adding rules, testing and the
developer tools.

## Name

![Heron](./docs/images/heron.jpg)

_Named after the [Heron](https://en.wikipedia.org/wiki/Heron) bird that watches over lakes since `lake` (in turn named after "Lean make") is the name of the build tool for Lean._
