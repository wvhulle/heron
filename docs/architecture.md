# Architecture

Heron runs inside the Lean compiler. Its rules are Lean code, compiled into a library that Lean
loads as a plugin or an import, and the `heron` command line tool reports and applies what those
rules find. [Style](style.md) explains how to write a rule.

## Lake targets

```mermaid
flowchart LR
  Cli[Cli]
  weir[weir]
  Heron[Heron library]
  RuleDevelopment[RuleDevelopment library]
  FixReporting[FixReporting library]
  plugin([plugin: shared library])
  heron([heron])
  selfLint([heron-self-lint])
  dumpSyntaxTree([dump-syntax-tree])

  Heron --> plugin
  Heron --> FixReporting
  Cli --> FixReporting
  weir --> FixReporting
  FixReporting --> heron
  Heron --> RuleDevelopment
  RuleDevelopment --> selfLint
  RuleDevelopment --> dumpSyntaxTree
```

`Heron` holds the rule framework and every rule, and is the only part a Lean project loads.
`FixReporting` builds the `heron` executable on [lean4-cli](https://github.com/leanprover/lean4-cli)
and [Weir](https://codeberg.org/wvhulle/weir). `RuleDevelopment` holds tools for rule authors:
a showcase, profiling, the syntax-tree dump and the self-lints that check how rules are written.

## Rules

```mermaid
flowchart TD
  elaborator[Lean elaborates a command] --> linter[Heron linter]
  linter -->|syntax kinds a rule declares| detect[rule detects a match]
  detect --> check{check or refactor?}
  check -->|check| diagnostic[diagnostic with explanation and source]
  diagnostic --> quickFix[quick fix in the editor]
  diagnostic --> fixRecord[fix record for the command line]
  check -->|refactor| codeAction[code action, only when the cursor is on the match]
```

A **check** runs on every command once `linter.heron` is on. A **refactor** never flags anything
and only answers code-action requests. Both match the syntax Lean has already parsed and
elaborated, ask the info tree for types and names, and build their fix as one quotation over the
matched node, so the user's comments and layout between the reused pieces stay as written. Rules
that replace an expression by an equal one name a lemma from Lean core instead, and its proof is
what makes the fix correct.

## How Heron reaches a project

```mermaid
flowchart LR
  lakefile[lakefile: plugin and linter.heron] --> rules
  perFile[import Heron in a file] --> rules
  serve[heron serve] --> rules
  scan[heron scan] --> rules
  rules[Heron rules inside Lean] --> editor[editor hints, quick fixes, refactors]
  rules --> build[warnings on lake build]
  rules --> records[fix records]
  records --> lint[lake lint and heron lint]
  rules --> scanReport[heron scan report and fixes]
```

The [lakefile setup](setup.md#lakefile-setup) loads the `plugin` target into every Lean process
of the project, and `lake lint` runs `heron lint`, which builds the project and reads the fix
records the build wrote. The [per-file import](setup.md#per-file-import) loads the same rules
through `import Heron`. Without project changes, `heron scan` elaborates the files itself and
`heron serve` runs the plugin in a language server of its own. In every case the plugin must be
built with the project's exact Lean version.

## `heron serve`

```mermaid
sequenceDiagram
  participant editor as Editor
  participant proxy as heron serve (Weir proxy)
  participant lake as lake serve with the plugin
  editor->>proxy: initialize
  proxy->>proxy: lean --version in the project
  alt plugin bundled or cached for that version
    proxy->>lake: start with the plugin
  else built from source
    proxy->>proxy: build the plugin from the matching lean/* branch, report progress
    proxy->>lake: start with the plugin
  else no plugin possible
    proxy-->>editor: stay idle, show the reason
  end
  editor->>proxy: open and edit files, code-action requests
  proxy->>lake: forward
  lake-->>proxy: all diagnostics and code actions
  proxy-->>editor: only Heron's diagnostics and code actions
```

Weir is a reusable proxy in front of `lake serve`; Heron only tells it its plugin target, how to
recognise its own diagnostics and code actions, and which repository holds the release branches.
[Editor setup](editor.md#progress-and-idle-states) describes the idle cases.

## Release branches

```mermaid
flowchart LR
  base[lean/v4.31.0: shared base] --> pin429[lean/v4.29.1]
  base --> pin430[lean/v4.30.0]
  base --> fork[lean-fork/v4.31.0]
  base --> from432[from Lean 4.32]
  from432 --> pins432[lean/v4.32.0 … lean/v4.34.1]
  from432 --> from435[from Lean 4.35]
  from435 --> pin435[pin 4.35.0]
  pin435 --> main[Weir frontend: main and lean/v4.35.0]
  pins432 -.->|plugin, as flake input| main
  pin429 -.-> main
  pin430 -.-> main
  base -.-> main
```

Each supported Lean release has its own branch, because the plugin must match the compiler
exactly. The branches share as much as possible:

- Changes that work on every toolchain live in the shared base.
- A workaround for a Lean API change is one step at the first minor version that needs it, and
  every newer branch builds on it.
- A branch adds only its toolchain pin.

`main` is the newest release plus the `heron serve` frontend. Its Nix package bundles the plugins
of all older stock branches, which it takes as flake inputs. The fork branch builds against
[a Lean fork](https://github.com/wvhulle/lean4) with richer hover popups.

## CI

```mermaid
flowchart LR
  flakeCheck[nix flake check] --> rules[rules: the library and every rule test]
  flakeCheck --> developerTools[developer-tools: the tools, their tests and the self-lints]
  flakeCheck --> lakefileSetup[lakefile-setup: a consumer project with the plugin]
  flakeCheck --> perFileImport[per-file-import: a consumer project that imports Heron]
  lakefileSetup --> probes[cold build, warnings, lake lint fixes, editor probes]
  perFileImport --> probes
```

The rule tests are compile-time assertions, so building the library runs them. The consumer
checks build a small project from scratch, compare its `lake lint --json` output with the expected
fixes and probe its language server. Woodpecker on Codeberg runs the same `nix flake check` on
every branch and fills the Cachix cache; the GitHub repository is a mirror.
