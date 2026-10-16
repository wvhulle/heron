import Lake

open System Lake DSL

package heron where
  version := v!"0.1.0"
  description :=
  "Refactoring and lint framework for Lean 4: checks with quick-fixes, refactor code actions, and clippy-style reporters"
  keywords := #["linter", "refactoring", "code-actions", "tooling"]
  homepage := "https://codeberg.org/wvhulle/heron"
  license := "Apache-2.0"

require Cli from git "https://github.com/leanprover/lean4-cli" @ "v4.29.0"

@[default_target] lean_lib Heron where
  globs := #[`Heron.*]
  defaultFacets := #[`lean_lib.shared]

@[default_target] lean_lib RuleDevelopment where globs := #[`RuleDevelopment.+]

lean_lib FixReporting where globs := #[`FixReporting.+]

lean_exe «dump-syntax-tree» where root := `RuleDevelopment.DumpSyntaxTree

lean_exe «heron-self-lint» where
  root := `RuleDevelopment.SelfLint
  supportInterpreter := true

lean_exe heron where
  root := `FixReporting.HeronCommand
  supportInterpreter := true

target plugin : Dynlib := do
  let some heron ← findLeanLib? `Heron
    | error "library `Heron` not found"
  heron.shared.fetch
