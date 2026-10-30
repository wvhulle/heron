# Development

How to build, test and release Heron. [Style](style.md) covers how to write rules.

## Development environment

With [elan](install.md#prerequisites) installed, a clone of Heron builds with plain Lake:

```sh
lake build                                  # the library, which runs every rule test
lake build && lake exe heron-self-lint      # the self-lints
```

### With Nix

This section only applies if you use Nix. `nix develop` gives a shell with elan
(`unmanaged-vanilla`, the default), and `nix develop .#managed-stock` one with the Nix-built Lean.

## Testing

Tests use compile-time assertion commands that verify rules at build time, so `lake build` runs
them. Failures appear as errors in the build output.

`#assertCheck` verifies that a check rule transforms a command into the expected result:

```lean
#assertCheck mergeConsecutiveIntros in
example : Nat → Nat → True := by intro a; intro b; exact trivial
becomes `(example : Nat → Nat → True := by intro a b; exact trivial)
```

`#assertRefactor` does the same for refactor rules:

```lean
#assertRefactor inline in
example : Nat := myConst
becomes `(example : Nat := (42))
```

`#assertIgnore` verifies that a rule produces no matches for the given command:

```lean
#assertIgnore mergeConsecutiveIntros in
example : Nat → Nat → True := by intro a; skip; intro b; exact trivial
```

## End-to-end checks

The end-to-end tests build small consumer projects from scratch.
[`EndToEndTests/ScenarioCheck.lean`](../EndToEndTests/ScenarioCheck.lean) runs them with
`lean --run`, and its editor probes talk LSP to `lake serve`. The `lakefile-setup` scenario
compares `lake lint --json` against
[`EndToEndTests/expected-fixes.json`](../EndToEndTests/expected-fixes.json), so update that file
when a rule's fixes change.

The plugin's `lean_lib` must keep the name of its root module, `Heron`, because Lean derives the
plugin's initializer from the `.so` file stem; find the file with `lake query heron/plugin` rather
than hardcoding its name. Check plugin changes with a cold consumer build, such as the
`lakefile-setup` check below: a warm local consumer keeps an old traced `.so` and hides loading
failures.

### CI with Nix

CI runs the rule tests, the self-lints and the end-to-end scenarios as Nix flake checks, so this
part needs Nix. The command is the same locally:

```sh
nix flake check -L --keep-going
```

Run one check with `nix build -L .#checks.x86_64-linux.<name>`; the checks are listed under
[CI](architecture.md#ci). On Lean 4.29 and 4.30 the editor probes are skipped, because those
language servers read `/etc/localtime`, which the Nix build environment does not have.

## Release branches

[Architecture](architecture.md#release-branches) shows the branch layout. To change it:

- Commit a change that works on every toolchain to the base, `lean/v4.31.0`, and rebase the other
  branches onto it.
- Commit a workaround for a Lean API change once, at the first minor that needs it, such as
  `from Lean 4.32`; every newer branch builds on it.
- A branch adds only its pin: `lean-toolchain`, the matching `require Cli … @ "vX.Y.0"` and
  `lake-manifest.json`.
- Push `main` and `lean/v4.35.0` together; they point at the same commit.

The Nix packaging adds two steps:

- Manifests for Lean releases that lean4-nix does not package go to `Lean4NixManifests/` in the
  base.
- `main`'s Nix package bundles the plugins of the older branches as flake inputs. After those
  branches change and are pushed, re-lock them on `main` with
  `nix flake update --refresh heron-lean-v4-…` before pushing `main`.

## Developer tools

Open [`RuleDevelopment/RuleShowcase.lean`](../RuleDevelopment/RuleShowcase.lean) in your editor to
see every rule fire at once. It imports `RuleDevelopment.RuleProfiling`, which adds the option
`heron.profile`; with it set, `#heronProfile` prints how long each enabled check took so far.

## Inspecting Lean syntax trees

When writing new checks or refactors, use `dump-syntax-tree` to inspect how Lean parses a given expression. This helps you find the correct `SyntaxKind`, child indices, and tree structure. Wrap snippets in a command (e.g. `def` or `example`) since the parser expects commands.

```sh
echo 'def f := pure ()' | lake exe dump-syntax-tree

# From a file
lake exe dump-syntax-tree myfile.lean

# Inline input
lake exe dump-syntax-tree --input 'example := match x with | some v => v | _ => 0'
```

The output is JSON. Pipe into `jq` for filtering:

```sh
echo 'def f := set { s with count := 0 }' | lake exe dump-syntax-tree | jq '.children[1].value'
```
