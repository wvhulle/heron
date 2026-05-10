# Contributing to Heron

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
