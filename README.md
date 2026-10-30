# Heron

**Heron finds non-idiomatic [Lean 4](https://github.com/leanprover/lean4) code and fixes it: in your editor, on `lake build`, and in CI.**

```lean
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
--^^^^^ Match on the parameters directly with `def f : A → B | pattern => …`
  | .saturday | .sunday => true
  | _ => false
```

The quick fix turns it into

```lean
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false
```

![The `Id.run` check in the editor](./docs/images/editor-popup.png)

## Documentation

- [Setup](docs/setup.md): add Heron to a Lake project, or use it without project changes, and
  pick the Heron ref for your Lean version
- [Install](docs/install.md): the `heron` command, built from source or from Nix
- [Editor setup](docs/editor.md): `heron serve` in Helix, Neovim and VS Code
- [Rules](docs/rules.md): checks and refactors, listing them and turning them off
- [Architecture](docs/architecture.md): how the targets, rules, server and release branches fit
  together
- [Style](docs/style.md): writing rules, testing and conventions for contributors

## Name

![Heron](./docs/images/heron.jpg)

_Named after the [Heron](https://en.wikipedia.org/wiki/Heron) bird that watches over lakes since `lake` (in turn named after "Lean make") is the name of the build tool for Lean._
