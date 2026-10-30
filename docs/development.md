# Development

How to set up a development environment, add a rule, run the checks and release Heron.
[Style](style.md) lists the code patterns rules must follow, and [Architecture](architecture.md)
shows how the parts fit together.

## Development environment

Install `git`, a C toolchain and [elan](install.md#prerequisites), then clone and build:

```sh
git clone https://github.com/wvhulle/heron && cd heron
lake build
```

elan installs the Lean version in `lean-toolchain`. To work on an older Lean release, check out
its `lean/v<version>` branch; see [Release branches](#release-branches).

### With Nix

This section only applies if you use Nix. `nix develop` gives a shell with elan
(`unmanaged-vanilla`, the default), and `nix develop .#managed-stock` one with the Nix-built Lean.

## Adding a rule

Checks go in [`Heron/Check/`](../Heron/Check), refactors in [`Heron/Refactor/`](../Heron/Refactor).
A rule named `RemoveElsePureUnit` consists of:

| File | Contents |
| --- | --- |
| `Heron/Check/RemoveElsePureUnit.lean` | the match struct, a `Check` (or `Refactor`) instance, and `register_check RemoveElsePureUnitMatch` (or `register_refactor`) at the end |
| `Heron/Check/RemoveElsePureUnit/Detects.lean` | one `#assertCheck … becomes` per rewrite the rule performs |
| `Heron/Check/RemoveElsePureUnit/Ignores.lean` | one `#assertIgnore` per `return #[]` or `none` branch in `detect`, so each guard against a false positive is pinned |

Then add `public import Heron.Check.RemoveElsePureUnit` to
[`Heron/Registry.lean`](../Heron/Registry.lean).

The instance sets `name`, a one-sentence `description` (which `heron rules` prints), `kinds`,
`detect`, `message`, `replacements` and `sources`;
[`RemoveElsePureUnit.lean`](../Heron/Check/RemoveElsePureUnit.lean) is a complete example.
Registration refuses a rule whose `kinds` is empty or names neither a node kind nor a category,
whose `within` names something that is not a node kind, or that lacks either test file.

A rule that rewrites an expression with an equation from Lean core is shorter; this is all of
[`ListMapMapToSingleMap.lean`](../Heron/Check/ListMapMapToSingleMap.lean):

```lean
private meta def ListMapMapToSingleMap := EquationRewriteMatch

private meta instance : Check ListMapMapToSingleMap := rewriteByEquation {
  name := `listMapMapToSingleMap
  description := "Suggests one `List.map` with a composed function instead of two consecutive maps."
  equation := ``List.map_map
  message := m!"Use one `List.map` with a composed function"
  label := m!"map fusion"
  sources := #[.hlint "Use map once"] }

register_check ListMapMapToSingleMap
```

Its tests have one `#assertCheck` per spelling the equation matches.
[Style](style.md#rewrite-expressions-with-an-equation) explains which equations work.

### Test commands

The tests are compile-time assertions, so `lake build` runs them and failures appear as errors in
the build output.

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

### Inspecting Lean syntax trees

Use `dump-syntax-tree` to find the node kind and shape a rule should match. Wrap snippets in a
command (e.g. `def` or `example`), since the parser expects commands.

```sh
echo 'def f := pure ()' | lake exe dump-syntax-tree
lake exe dump-syntax-tree myfile.lean
lake exe dump-syntax-tree --input 'example := match x with | some v => v | _ => 0'
```

The output is JSON. Pipe it into `jq` to filter:

```sh
echo 'def f := set { s with count := 0 }' | lake exe dump-syntax-tree | jq '.children[1].value'
```

### Seeing rules fire

Open [`RuleDevelopment/RuleShowcase.lean`](../RuleDevelopment/RuleShowcase.lean) in your editor to
see every rule fire at once. It imports `RuleDevelopment.RuleProfiling`, which adds the option
`heron.profile`; with it set, `#heronProfile` prints how long each enabled check took so far.

## Running the checks

Before merging a rule, run:

```sh
lake build                                # the library and every rule test
lake build && lake exe heron-self-lint    # the forbidden APIs from the style guide
```

Then run the rule on real code: inside a built checkout of a sizeable project at the tag of
Heron's toolchain, run `heron scan --rule <name> <dir>` and read every hit. Keep that checkout
outside Heron's tree. On Mathlib-scale projects, lower `--jobs` or `--memory` if the scan uses up
too much memory, and run one such scan at a time.

### End-to-end checks

The end-to-end tests build small consumer projects from scratch.
[`EndToEndTests/ScenarioCheck.lean`](../EndToEndTests/ScenarioCheck.lean) runs them with
`lean --run`, and its editor probes talk LSP to `lake serve`. The `lakefile-setup` scenario
compares `lake lint --json` against
[`EndToEndTests/expected-fixes.json`](../EndToEndTests/expected-fixes.json), so update that file
when a rule's fixes change.

The plugin's `lean_lib` must keep the name of its root module, `Heron`, because Lean derives the
plugin's initializer from the `.so` file stem; find the file with `lake query heron/plugin` rather
than hardcoding its name. Check plugin changes with a cold consumer build, such as the
`lakefile-setup` check: a warm local consumer keeps an old traced `.so` and hides loading failures.

### CI with Nix

CI runs the rule tests, the self-lints and the end-to-end scenarios as Nix flake checks, so this
part needs Nix. The command is the same locally:

```sh
nix flake check -L --keep-going
```

Run one check with `nix build -L .#checks.x86_64-linux.<name>`; the checks are listed under
[CI](architecture.md#ci). On Lean 4.29 and 4.30 the editor probes are skipped, because those
language servers read `/etc/localtime`, which the Nix build environment does not have.

## Changes

- **One concern per commit.** Split metadata, CI, docs and code changes, and a toolchain pin from
  an import fix. Build each branch head before pushing.
- **Fix by reorganizing.** Before adding a mechanism, check whether moving or narrowing existing
  code fixes the problem; a fix should end with less code than it started with.
- **Resolve names at the boundary.** Turn names given on the command line into the objects they
  name where they are parsed, for example `--rule` into the registered rule entries, and pass
  those down instead of names or options.
- **Plain entry points.** Each subcommand's flags live in its own module. Tooling runs as
  `lake exe`, test logic is Lean, and the flake only wires things together: no shell glue and no
  symlinks.
- **No external code in the tree.** Never add other repositories, corpus workspaces or their
  manifests.

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
