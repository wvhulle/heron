# Style

How rules for Heron are written, and the conventions for changing the repository.
[Development](development.md) covers building, testing and the developer tools, and
[Architecture](architecture.md) shows how the parts fit together.

## Writing a rule

Check rules live in [`Heron/Check/`](../Heron/Check), refactor rules in
[`Heron/Refactor/`](../Heron/Refactor). A rule is one file `<Rule>.lean` with a match struct, a
one-sentence `description` (`heron rules` prints it), `detect`, `message`, `replacements`
and `sources`, plus the tests `<Rule>/Detects.lean` and `<Rule>/Ignores.lean`. The file ends
with `register_check <Match>` or `register_refactor <Match>`. `kinds` lists syntax node kinds or
syntax categories: `` kinds := #[`command] `` runs a rule on every command, including commands
from libraries Heron does not know, such as Mathlib's `lemma`. Registration refuses a rule whose
`kinds` is empty or names neither a node kind nor a category, whose `within` names something that
is not a node kind, or that lacks either test file.

### Rules that apply an equation

A rule that replaces one expression by an equal one, as most hlint hints do, names the equation
instead of writing `detect` and `replacements`. The whole rule is
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

`List.map_map` states `List.map g (List.map f l) = List.map (g ∘ f) l`. The rule runs on every
command and matches the left-hand side against every subterm's elaborated form, so every
spelling is found, operators and dot chains included:

```lean
List.map f (List.map g xs)   -- becomes List.map (f ∘ g) xs
(xs.map g).map f             -- becomes List.map (f ∘ g) xs
xs.map g |>.map f            -- becomes List.map (f ∘ g) xs
!!b                          -- Bool.not_not: becomes b
```

Only subterms whose head is the equation's head constant are unified, so the cost stays close to
one comparison per subterm, and each spelling belongs to one rule: `Option.map f (Option.map g o)`
to `Option.map_map`, while `f <$> g <$> o`, whose head is the class method `Functor.map`, belongs to
the Functor law (`Functor.map_map`).

The fix prints the right-hand side with the matched source pieces (`f`, `g`, `xs`) in place of
the equation's variables. A piece with no source of its own, such as a coerced argument, is
printed from its elaborated form. The fix is only offered when the printed replacement elaborates
back to the equation's instantiated right-hand side, which also catches a lemma binder capturing a
source variable; binders that would capture one are renamed first, so `List.foldr_map` prints
`fun x_1 y_1 => x (f x_1) y_1` when the source already uses `x` and `y`.
The proof of the equation is what makes the fix correct. Instance arguments the left-hand side does
not fix are synthesized, and a match is refused when one cannot be or when a hypothesis is left.

The equation must come from Lean's core library: the rule looks it up in the user's environment,
and a project that loads Heron as a plugin does not import Heron's own declarations, so a lemma
proved in Heron would never be found there. When core states the equation the other way round,
set `rightToLeft`; [`ListFlattenOfMapToFlatMap.lean`](../Heron/Check/ListFlattenOfMapToFlatMap.lean)
reads `List.flatMap_def` backwards:

```lean
  equation := ``List.flatMap_def
  rightToLeft := true
```

Tests are the usual `Detects.lean` and `Ignores.lean`, with one `#assertCheck` per spelling.

Rules work the way the linters in Lean core and Mathlib do: they match the structure Lean has
already parsed and elaborated, and never go back to the source text. Concretely:

1. **Match with quotation patterns at the declared kinds.** `kinds` lists the node kinds the rule
   fires on and the framework dispatches to `detect` there; `detect` then matches with
   `` `(doElem| if $cond then $body) ``-style patterns whose antiquotations name every part the
   rule needs, and stores them as `TSyntax` in the match struct. Use
   [`dump-syntax-tree`](development.md#inspecting-lean-syntax-trees) to find the kind and the
   shape. `within` restricts the rule to nodes below one of the listed
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
4. **Test every shape and every guard** with the [assertion commands](development.md#testing).
   `Detects.lean` has one `#assertCheck … becomes` per rewrite the rule performs. `Ignores.lean` has one `#assertIgnore` per `return #[]` branch in
   `detect`, so each guard against a false positive is pinned.
5. **Name the sources.** `sources` lists where the idea comes from, from `Heron.Source`: a book
   section, the Lean standard library or Mathlib style guide, an hlint hint or a Clippy lint.
   Leave `sources` out until you have found one.
6. **Run it on real code before merging**: inside a built checkout of a sizeable project at the
   toolchain's tag, `heron scan --rule <name> <dir>`, and read every hit.

### What the self-lints reject

Five checks in `RuleDevelopment/SelfLint/` run over `Heron/Check/*.lean`, `Heron/Refactor/*.lean`
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

## Conventions

- **One concern per commit.** Split metadata, CI, docs and code changes, and a toolchain pin from
  an import fix. Build each branch head before pushing.
- **Fix by reorganizing.** Before adding a mechanism, check whether moving or narrowing existing
  code fixes the problem; a fix should end with less code than it started with. No fallbacks that
  produce text when the real path fails, as they hide formatting defects.
- **Rule hygiene is a Heron check.** Constraints on how rules are written are checks in
  `RuleDevelopment/SelfLint/`, matched on the info tree like any other rule, never scans of names
  or strings. A file is exempted with `set_option linter.<check> false`, and that list only
  shrinks.
- **Let the structure carry the meaning.** When a field would duplicate what another already
  encodes, make the other an `Option` instead of adding a boolean.
- **No placeholder values.** Leave unknown metadata such as `sources` empty until a real value is
  found; a placeholder reads as real data.
- **Resolve names at the boundary.** Turn names given on the command line into the objects they
  name where they are parsed, for example `--rule` into the registered rule entries, and pass
  those down instead of names or options.
- **Plain entry points.** Each subcommand's flags live in its own module. Tooling runs as
  `lake exe`, test logic is Lean, and the flake only wires things together through lean4-nix and
  Weir: no shell glue and no symlinks.
- **No external code in the tree.** Never add other repositories, corpus workspaces or their
  manifests. Try a rule on a separate checkout of a real project at the tag of Heron's toolchain.
