# Contributing to Heron

## Adding New Rules

Check rules live in [`Heron/Check/`](./Heron/Check), refactor rules in [`Heron/Refactor/`](./Heron/Refactor). Each rule file contains:

- A match data struct describing what was detected
- A `detect` function that scans user source code
- A set of `replacements` to fix a single match
- Inline tests for false positives, replacements, and negatives

## Testing

Tests use compile-time assertion commands that verify rules at build time. Failures appear as errors in the build output.

`#assertCheck` verifies that a check rule transforms a command into the expected result:

```lean
#assertCheck mergeIntros in
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
#assertIgnore mergeIntros in
example : Nat → Nat → True := by intro a; skip; intro b; exact trivial
```

## Things not to use in rule implementations

You likely should not access the `raw` field of syntax objects. You can attach extra information to patterns inside quotations so that the extracted object has the data you need without raw access.

Dont index into the fields of syntax objects with integer indices and unchecked access. Use anti-quotations instead.

## Inspecting Lean syntax trees

When writing new checks or refactors, use `dump-ast` to inspect how Lean parses a given expression. This helps you find the correct `SyntaxKind`, child indices, and tree structure. Wrap snippets in a command (e.g. `def` or `example`) since the parser expects commands.

```sh
echo 'def f := pure ()' | lake exe dump-ast

# From a file
lake exe dump-ast myfile.lean

# Inline input
lake exe dump-ast --input 'example := match x with | some v => v | _ => 0'
```

The output is JSON. Pipe into `jq` for filtering:

```sh
echo 'def f := set { s with count := 0 }' | lake exe dump-ast | jq '.children[1].value'
```
