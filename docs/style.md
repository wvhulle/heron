# Style

Which code patterns a Heron rule should use and which it must avoid.
[Development](development.md#adding-a-rule) explains where a rule goes and how to test it.

Rules work the way the linters in Lean core and Mathlib do: they match the structure Lean has
already parsed and elaborated, and never go back to the source text.

## Match with quotation patterns at the declared kinds

`kinds` lists the node kinds or syntax categories the rule fires on, and the framework dispatches
to `detect` there. `detect` then matches with `` `(doElem| if $cond then $body) ``-style patterns
whose antiquotations name every part the rule needs, and stores them as `TSyntax` in the match
struct.

`` kinds := #[`command] `` runs a rule on every command, including commands from libraries Heron
does not know, such as Mathlib's `lemma`. `within` restricts the rule to nodes below one of the
listed kinds, e.g. `` kinds := #[``Term.app], within := #[``Command.declSig] `` for types written
in a signature, the way Lean core's `UnusedVariables` matches on the syntax stack. A rule that
analyses a whole declaration fires at `` ``Command.declaration ``.

The framework does the walking; a rule never walks the tree itself.

## Take meaning from elaboration, not from spelling

When a rule depends on a type, an instance, a binder or what a name resolves to, ask the info
tree: `runMetaMForSyntax`, `runMetaMForEachExactSyntax`, `collectTermInfos`,
`elaboratesToApplicationOf`, `outerHasMonadInstance` and
`elaboratesWithoutErrorsInProbeNamespace` in `Heron/Rule.lean`, `Heron/Check.lean` and
`Heron/Monad.lean`. `Lean.Linter.ConstructorAsVariable` and `Lean.Linter.UnusedVariables` in Lean
core are the models; `Heron/Check/RemoveLetWildcardOnUnitAction.lean` and
`NestedExprAppToMkAppN.lean` are local ones.

An analysis that follows a variable follows its `FVarId`, not its written name.

## Build the fix with one quotation

Build the replacement as one quotation over the whole matched node, reusing the matched `TSyntax`
pieces; delete with `Syntax.missing`; make literals with `quote`. Set `prettyPrint` when the node
is not a term (`PrettyPrinter.ppCategory `doElem`, or a parser's formatter for binders and match
arms).

`Replacement.toTextEdits` prints the quotation once and edits only the gaps between reused pieces,
so their source text, comments and layout stay as written. Do not split a fix into token-sized
replacements to protect user code, and do not add a fallback that produces text when the
quotation cannot be printed: it hides the formatting defect.
`Heron/Check/TupleMatchToSimultaneousMatch.lean` and `RemoveIdRunWithoutEffects.lean` show the
shape; `Lean.Elab.Tactic.Simpa` is the upstream example.

A fix that replaces a run of consecutive nodes, separators included, uses
`mkNullNode #[first, last]` as its `oldSyntax`: the null node only spans the source nodes, as in
`Simpa`. A check that only flags code leaves `replacements` out, and the listing then says it has
no automatic fix.

## Rewrite expressions with an equation

A rule that replaces one expression by an equal one, as most hlint hints do, names the equation
instead of writing `detect` and `replacements`, as in
[`ListMapMapToSingleMap.lean`](../Heron/Check/ListMapMapToSingleMap.lean):

```lean
  equation := ``List.map_map
```

`List.map_map` states `List.map g (List.map f l) = List.map (g ∘ f) l`. The rule matches the
left-hand side against every subterm's elaborated form, so every spelling is found, operators and
dot chains included:

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
`fun x_1 y_1 => x (f x_1) y_1` when the source already uses `x` and `y`. The proof of the equation
is what makes the fix correct. Instance arguments the left-hand side does not fix are
synthesized, and a match is refused when one cannot be or when a hypothesis is left.

The equation must come from Lean's core library: the rule looks it up in the user's environment,
and a project that loads Heron as a plugin does not import Heron's own declarations, so a lemma
proved in Heron would never be found there. When core states the equation the other way round,
set `rightToLeft`; [`ListFlattenOfMapToFlatMap.lean`](../Heron/Check/ListFlattenOfMapToFlatMap.lean)
reads `List.flatMap_def` backwards:

```lean
  equation := ``List.flatMap_def
  rightToLeft := true
```

## Metadata

- `sources` lists where the idea comes from, from `Heron.Source`: a book section, the Lean
  standard library or Mathlib style guide, an hlint hint or a Clippy lint. Leave it out until you
  have found one; never add a placeholder source, which reads as real data.
- When a field would duplicate what another already encodes, make the other an `Option` instead
  of adding a boolean, as `replacements` does for whether a check has a fix.

## Forbidden APIs

The self-lints reject these in rule files, and any finding fails the build:

| Check | Rejects |
| --- | --- |
| `positionalSyntaxAccess` | `getArg`, `getArgs`, `getNumArgs`, `stx[i]` |
| `syntaxKindOrAtomInspection` | `getKind`, `isOfKind`, `getAtomVal`, `getHead?` |
| `syntheticSyntaxConstruction` | `mkAtom`, `mkNode`, `Syntax.mkNumLit`, `Syntax.ofRange`, `Syntax.node`/`.atom`/`.ident` patterns, and `mkIdent` of a literal name (write it in a quotation under `set_option hygiene false in`) |
| `sourcePositionInRule` | `getPos?`, `getTailPos?`, `getRange?`, `FileMap` lookups |
| `sourceTextInRule` | `reprint`, `getSubstring?`, `Name.toString`, `String.splitOn`, `trimAscii*`, `startsWith`, `endsWith` |

No rule disables them. When one seems to be in the way, the framework is missing a helper, and the
helper belongs in `Heron/Rule.lean`, `Heron/Check.lean` or `Heron/Monad.lean`, which the
self-lints do not check. New constraints on how rules are written become self-lints too: checks
matched on the info tree like any other rule, never scans of names or strings.
