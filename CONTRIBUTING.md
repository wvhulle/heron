# Contributing to Heron

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
3. **Build the fix with one quotation** over the whole matched node, reusing the matched
   `TSyntax` pieces; delete with `Syntax.missing`; make literals with `quote`. Set
   `prettyPrint` when the node is not a term (`PrettyPrinter.ppCategory `doElem`, or a parser's
   formatter for binders and match arms). `Replacement.toTextEdits` prints the quotation once and
   edits only the gaps between reused pieces, so their source text, comments and layout stay as
   written; do not split a fix into token-sized replacements to protect user code.
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

Five checks in `DevExecutables/SelfLint/` run over `Heron/Check/*.lean`, `Heron/Refactor/*.lean`
and their own files in CI (the `developer-tools` check), and any finding fails the build. They live
outside the `Heron` library, so `linter.heron` never turns them on in other projects:

| Check | Rejects |
| --- | --- |
| `positionalSyntaxAccess` | `getArg`, `getArgs`, `getNumArgs`, `stx[i]` |
| `syntaxKindOrAtomInspection` | `getKind`, `isOfKind`, `getAtomVal`, `getHead?` |
| `syntheticSyntaxConstruction` | `mkAtom`, `mkNode`, `Syntax.mkNumLit`, `Syntax.ofRange`, `Syntax.node`/`.atom`/`.ident` patterns, and `mkIdent` of a literal name (write it in a quotation under `set_option hygiene false in`) |
| `sourcePositionInRule` | `getPos?`, `getTailPos?`, `getRange?`, `FileMap` lookups |
| `sourceTextInRule` | `reprint`, `getSubstring?`, `Name.toString`, `String.splitOn`, `trimAscii*`, `startsWith`, `endsWith` |

Run them locally with `lake build && lake exe heron-self-lint`. No rule disables them; when one
seems to be in the way, the framework is missing a helper, and the helper belongs in
`Heron/Rule.lean`, `Heron/Check.lean` or `Heron/Monad.lean`, which the self-lints do not check.

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

## Flake checks

CI runs one command, and it is the same locally:

```sh
nix flake check -L --keep-going
```

It builds four checks; run one with `nix build -L .#checks.x86_64-linux.<name>`:

| Check | What it verifies |
| --- | --- |
| `rules` | the library with all `#assert*` tests above |
| `developer-tools` | the developer tools and their tests, then `lake exe heron-self-lint` |
| `lakefile-setup` | a consumer with the lakefile setup: a cold build, Heron's warnings, `lake lint --json` against [`EndToEndTests/expected-fixes.json`](./EndToEndTests/expected-fixes.json), and hints and quick fixes in the editor |
| `per-file-import` | a consumer that imports Heron in one file: the build and the editor |

[`EndToEndTests/ScenarioCheck.lean`](./EndToEndTests/ScenarioCheck.lean) runs both consumer checks
with `lean --run`; its editor probes talk LSP to `lake serve` and `heron-language-server`. On Lean
4.29 and 4.30 the probes are skipped, because those language servers read `/etc/localtime`, which
the Nix build environment does not have.

## Developer tools

Open [`DevExecutables/RuleShowcase.lean`](./DevExecutables/RuleShowcase.lean) in your editor to
see every rule fire at once. It imports `DevExecutables.RuleProfiling`, which adds the option
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
