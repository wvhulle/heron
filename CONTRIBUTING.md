# Contributing to Heron

## Repository layout

- [`Heron/`](./Heron): the rules, built as the `@heron/plugin` shared library. Checks live in
  [`Heron/Check/`](./Heron/Check), refactors in [`Heron/Refactor/`](./Heron/Refactor).
- [`Executables/`](./Executables): only the roots of the three user tools:
  - `LakeLintDriver`: `heron`, the driver behind `lake lint`.
  - `StandaloneScan`: `heron-scan`.
  - `SecondLanguageServer`: `heron-language-server`.
- [`ToolSupport/`](./ToolSupport): code the tools share, kept out of the plugin library. A file
  name that starts with a tool's root name (`LakeLint*`, `StandaloneScan*`) serves that tool;
  `FixReportRendering` and `HeronPluginLocation` are used by several.
- [`DeveloperTools/`](./DeveloperTools): `dump-syntax-tree` and `RuleShowcase.lean`, see
  [Developer tools](#developer-tools).
- [`EndToEndTests/`](./EndToEndTests): one directory per usage scenario (`LakefileSetup`,
  `PerFileImport`, `NoProjectChanges`), each a small Lake project with the Nu scripts that test
  it. `SampleConsumerLibrary` holds the code the first and last scenarios run Heron on, and
  `expected-fixes.json` the fixes Heron must report for it.
- [`docs/`](./docs): user documentation linked from the README.
- [`Lean4NixManifests/`](./Lean4NixManifests): Lean toolchains that lean4-nix does not package
  yet.

## Adding New Rules

Check rules live in [`Heron/Check/`](./Heron/Check), refactor rules in [`Heron/Refactor/`](./Heron/Refactor). Each rule file contains:

- A match data struct describing what was detected
- A `detect` function that scans user source code
- A set of `replacements` to fix a single match
- The `sources` the rule is based on, from `Heron.Source`: a book section, the Lean standard
  library or Mathlib style guide, an hlint hint or a Clippy lint. List every source you used and
  add the same line under the rule in [docs/Rules.md](./docs/Rules.md). Leave `sources` out
  until you have found one.
- Inline tests for false positives, replacements, and negatives

## Testing

Tests use compile-time assertion commands that verify rules at build time. Failures appear as errors in the build output.

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

## Things not to use in rule implementations

You likely should not access the `raw` field of syntax objects. You can attach extra information to patterns inside quotations so that the extracted object has the data you need without raw access.

Dont index into the fields of syntax objects with integer indices and unchecked access. Use anti-quotations instead.

## End-to-end tests

Each usage scenario has its own checks, named after it, which CI runs as separate steps:

```sh
nix build -L .#checks.x86_64-linux.no-project-changes-editor
```

The list is in [`.woodpecker/build.yaml`](./.woodpecker/build.yaml). The `rules` check builds
the library with all `#assert*` tests above.

## Developer tools

Open [`DeveloperTools/RuleShowcase.lean`](./DeveloperTools/RuleShowcase.lean) in your editor to
see every rule fire at once.

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
