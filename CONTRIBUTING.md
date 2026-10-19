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
- [`DeveloperTools/`](./DeveloperTools): `dump-syntax-tree`, `heron-self-lint` and
  `RuleShowcase.lean`, see [Developer tools](#developer-tools) and
  [What the self-lints reject](#what-the-self-lints-reject).
- [`EndToEndTests/`](./EndToEndTests): one directory per usage scenario (`LakefileSetup`,
  `PerFileImport`, `NoProjectChanges`), each a small Lake project with the Nu scripts that test
  it. `SampleConsumerLibrary` holds the code the first and last scenarios run Heron on, and
  `expected-fixes.json` the fixes Heron must report for it.
- [`docs/`](./docs): user documentation linked from the README.
- [`Lean4NixManifests/`](./Lean4NixManifests): Lean toolchains that lean4-nix does not package
  yet.

## Writing a rule

Check rules live in [`Heron/Check/`](./Heron/Check), refactor rules in
[`Heron/Refactor/`](./Heron/Refactor). A rule is one file `<Rule>.lean` with a match struct, a
one-sentence `description` (`heron-scan rules` prints it), `detect`, `message`, `replacements`
and `sources`, plus the tests `<Rule>/Detects.lean` and `<Rule>/Ignores.lean`. The file ends
with `register_check <Match>` or `register_refactor <Match>`. Registration refuses a rule whose
`kinds` is empty, whose `kinds` or `within` name something that is not a syntax node kind, or
that lacks either test file.

Rules work the way the linters in Lean core and Mathlib do: they match the structure Lean has
already parsed and elaborated, and never go back to the source text. Concretely:

1. **Match with quotation patterns at the declared kinds.** `kinds` lists the node kinds the rule
   fires on and the framework dispatches to `detect` there; `detect` then matches with
   `` `(doElem| if $cond then $body) ``-style patterns whose antiquotations name every part the
   rule needs, and stores them as `TSyntax` in the match struct. Use `dump-syntax-tree` (below)
   to find the kind and the shape. `within` restricts the rule to nodes below one of the listed
   kinds, e.g. `` kinds := #[``Term.app], within := #[``Command.declSig] `` for types written in
   a signature, the way Lean core's `UnusedVariables` matches on the syntax stack. A rule that
   analyses a whole declaration fires at `` ``Command.declaration ``. The framework does the
   walking; a rule never walks the tree itself.
2. **Take meaning from elaboration, not from spelling.** When a rule depends on a type, an
   instance, a binder or what a name resolves to, ask the info tree: `runMetaMForSyntax`,
   `runMetaMForEachExactSyntax`, `collectTermInfos`, `elaboratesToApplicationOf`,
   `outerHasMonadInstance` and `elaboratesWithoutErrorsInProbeNamespace` in `Heron/Rule.lean`,
   `Heron/Check.lean` and `Heron/Monad.lean`. `Lean.Linter.ConstructorAsVariable` and
   `Lean.Linter.UnusedVariables` in Lean core are the models;
   `Heron/Check/RemoveLetWildcardOnUnitAction.lean` and `NestedExprAppToMkAppN.lean` are local
   ones. An analysis that follows a variable follows its `FVarId`, not its written name.
3. **Build the fix with a quotation** in the replacement's `category`, reusing the matched
   `TSyntax` pieces; delete with `Syntax.missing`; make literals with `quote`.
   `Heron/Check/TupleMatchToSimultaneousMatch.lean` and `RemoveIdRunWithoutEffects.lean` show
   the shape; `Lean.Elab.Tactic.Simpa` is the upstream example. A fix that replaces a run of
   consecutive nodes, separators included, uses `mkNullNode #[first, last]` as its
   `oldSyntax`: the null node only spans the source nodes, as in `Simpa`. A check that only
   flags code leaves `replacements` out, and the listing then says it has no automatic fix.
4. **Test every shape and every guard.** `Detects.lean` has one `#assertCheck … becomes` per
   rewrite the rule performs. `Ignores.lean` has one `#assertIgnore` per `return #[]` branch in
   `detect`, so each guard against a false positive is pinned.
5. **Name the sources.** `sources` lists where the idea comes from, from `Heron.Source`: a book
   section, the Lean standard library or Mathlib style guide, an hlint hint or a Clippy lint.
   Leave `sources` out until you have found one.
6. **Run it on real code before merging**: inside a built checkout of a sizeable project at the
   toolchain's tag, `heron-scan --rule <name> <dir>`, and read every hit.

### What the self-lints reject

Five of Heron's own checks run over `Heron/Check/*.lean` and `Heron/Refactor/*.lean` in CI
(the `rule-hygiene` check), and any finding fails the build:

| Check | Rejects |
| --- | --- |
| `positionalSyntaxAccess` | `getArg`, `getArgs`, `getNumArgs`, `stx[i]`, `subtreeNodes`, `signatureNodes` |
| `syntaxKindOrAtomInspection` | `getKind`, `isOfKind`, `getAtomVal`, `getHead?` |
| `syntheticSyntaxConstruction` | `mkAtom`, `mkNode`, `Syntax.mkNumLit`, `Syntax.ofRange`, `Syntax.node`/`.atom`/`.ident` patterns, and `mkIdent` of a literal name (write it in a quotation under `set_option hygiene false in`) |
| `sourcePositionInRule` | `getPos?`, `getTailPos?`, `getRange?`, `FileMap` lookups |
| `sourceTextInRule` | `reprint`, `getSubstring?`, `Name.toString`, `String.splitOn`, `trimAscii*`, `startsWith`, `endsWith` |

Run them locally with `lake build && lake exe heron-self-lint`. A rule written before these
checks existed may carry `set_option linter.<check> false` at the top of its file; that list
only shrinks, and a new rule never gets one.

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
