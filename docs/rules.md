# Rules

Heron has two kinds of rules. **Checks** run on every command once `linter.heron` is on; each
underlines the code it flags and, for most checks, offers a quick fix. **Refactors** never flag
anything and appear in the editor's code-action menu when the cursor is on code they can rewrite.

Hovering a check's underline explains the rule, links to the book section, style guide or other
linter it is based on, and names the option that turns it off. For the example in the README, the
source is the
[Pattern-matching definitions](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#pattern-matching-definitions)
section of _Functional Programming in Lean_, and the option is
`linter.matchOnParametersToPatternMatchingDefinition`.

## Listing the rules

`heron rules` prints every rule with its description and sources:

```sh
heron rules
heron rules --json   # machine-readable
```

In a project that requires Heron, run it as `lake exe heron rules`. Without a `heron` binary, see
[Install](install.md). `heron --help` lists the subcommands, and `heron <subcommand> --help` their
flags.

## Turning a rule off

In a file:

```lean
set_option linter.<rule> false
```

For the whole project, in `lakefile.lean`:

```lean
leanOptions := #[⟨`linter.heron, true⟩, ⟨`linter.<rule>, false⟩]
```
