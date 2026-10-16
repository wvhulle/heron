# Heron

**Heron finds non-idiomatic [Lean 4](https://github.com/leanprover/lean4) code and fixes it: in your editor, on `lake build`, and in CI.**

```lean
example : Nat → Nat → True := by intro a; intro b; exact trivial
--                               ^^^^^^^^^^^^^^^^ Merge intros: replace with `intro a b`
```

![The `Id.run` check in the editor](./screenshots/popup.png)

## Quick start

1. In your project's `lakefile.lean`, pick the Heron ref that matches your `lean-toolchain` (see
   [Supported Lean versions](#supported-lean-versions)):

   ```lean
   require heron from git "https://github.com/wvhulle/heron" @ "main"

   package «your_pkg» where
     leanOptions := #[⟨`linter.heron, true⟩]
     plugins := #[`@heron/plugin]
     lintDriver := "heron/heron"
   ```

2. Run `lake build`. Heron's warnings appear for every module, without any `import Heron`.
3. Run `lake lint` for a report of all fixes, or `lake lint -- --fix` to apply them.

`lakefile.toml` cannot refer to a dependency's targets. Convert it with
`lake translate-config lean`, or use the [per-file setup](#per-file-import).

## What you get

- **In the editor:** checks underline code and offer a quick-fix on the light bulb. Refactors
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

## Rules

Checks (enabled by `linter.heron`):

| Rule | Suggests |
| --- | --- |
| `boolMatchToIf` | `if … then … else …` instead of matching on `Bool` |
| `exceptToExceptT` | `ExceptT` instead of nesting `Except` |
| `exprAppChainToMkAppN` | `mkAppN` instead of nested `Expr.app` |
| `funMatchToMatchFun` | `fun \| …` pattern-matching syntax |
| `funToCdot` | `·` instead of an explicit lambda |
| `getSetToModify` | `modify` instead of `get`/`set` |
| `ifNotToUnless` | `unless` instead of `if not` |
| `matchToIfLet` | `if let` instead of a two-arm `match` with a wildcard |
| `mergeBinders` | merging binders with the same type |
| `mergeIntros` | merging consecutive `intro`s |
| `mergeMatchArms` | merging match arms with identical right-hand sides |
| `natLiteralPatterns` | `0` and `n + 1` instead of `Nat.zero` and `Nat.succ n` |
| `optionToOptionT` | `OptionT` instead of nesting `Option` |
| `optionWrapFilter` | `guard` in an `Option` `do`-block instead of `some _ \|>.filter _` |
| `redundantElsePureUnit` | dropping a redundant `else pure ()` |
| `redundantLetWildcard` | dropping a redundant `let _ ←` |
| `rflToExactRfl` | `exact rfl` instead of `rfl` |
| `syntaxKindCheck` | antiquotation patterns instead of comparing `Syntax.getKind` |
| `syntaxRawAccess` | a typed pattern or method instead of `.raw` on `TSyntax` |
| `tupleMatchToSimultaneous` | simultaneous matching instead of matching on a tuple |
| `unnecessaryIdRun` | removing an unnecessary `Id.run do` |
| `unnecessaryMut` | removing an unnecessary `mut` |

Refactors (code actions on a selection): `bindToDo` (`>>=` to do-notation), `flipIf` (swap `if`
branches), `inline` (inline a definition or `let`), `inlineAllConst` (inline every use of a
definition).

Turn a rule off with `set_option linter.<rule> false` in a file, or ``⟨`linter.<rule>, false⟩``
in `leanOptions`.

## Other ways to run Heron

### Per-file import

Require Heron (also possible in `lakefile.toml`) and enable it in the files you want checked:

```toml
[[require]]
name = "heron"
git = "https://github.com/wvhulle/heron"
rev = "main"
```

```lean
import Heron
set_option linter.heron true
```

### Without changing your project (Nix)

Build your project, then run `heron-scan` from the Heron ref that matches your toolchain. It
needs no `require`, plugin or `import`, but it re-elaborates the files itself, so it is slower
than the plugin setup on large projects.

```sh
lake build
nix run github:wvhulle/heron/main -- Consumer        # check a library or directory
nix run github:wvhulle/heron/main -- --fix Foo.lean  # apply fixes
```

### Executables

Any project that requires Heron can run its executables with `lake exe`:

| Command | What it does |
| --- | --- |
| `lake exe heron` | What `lake lint` runs: builds your targets with the plugin, then prints the fixes. Adds `--no-build` to read the last build's results. |
| `lake exe heron-scan` | Elaborates the targets itself; needs no plugin. Adds `--per-file`, `--no-cache`, `--no-parallel`, and reads stdin with `-`. |

Both accept `--json`, `--fix`/`--apply` and `--color`/`--no-color`.

```sh
lake exe heron-scan --fix Foo/Bar.lean
echo 'def f := fun x => x + 1' | lake exe heron-scan -
```

## Supported Lean versions

Heron runs inside the Lean compiler, so it must be built with exactly your project's Lean
version. Use the ref that matches your `lean-toolchain`:

| Your `lean-toolchain` | Heron ref |
| --- | --- |
| `leanprover/lean4:v4.35.0` | `main` |
| `leanprover/lean4:v4.31.0` | `lean/v4.31.0` |
| `leanprover/lean4:v4.30.0` | `lean/v4.30.0` |
| `leanprover/lean4:v4.29.1` | `lean/v4.29.1` |
| [wvhulle/lean4](https://github.com/wvhulle/lean4) fork | `lean-fork/v4.31.0` |

The `lean-fork/v4.31.0` branch adds features that need the fork: hover popups with the full
explanation, related-information labels, and import-analysis checks. The repository is mirrored to
GitHub, so `https://codeberg.org/wvhulle/heron` works as well.

## Contributing

See [CONTRIBUTING.md](./CONTRIBUTING.md) for adding rules, testing and inspecting syntax trees.

## Name

![Heron](./heron.jpg)

_Named after the [Heron](https://en.wikipedia.org/wiki/Heron) bird that watches over lakes since `lake` (in turn named after "Lean make") is the name of the build tool for Lean._
