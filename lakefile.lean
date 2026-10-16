import Lake

open System Lake DSL

package heron where
  version := v!"0.1.0"
  description :=
  "Refactoring and lint framework for Lean 4: checks with quick-fixes, refactor code actions, and clippy-style reporters"
  keywords := #["linter", "refactoring", "code-actions", "tooling"]
  homepage := "https://codeberg.org/wvhulle/heron"
  license := "Apache-2.0"

@[default_target] lean_lib Heron where
  globs := #[`Heron.*]
  defaultFacets := #[`lean_lib.shared]

lean_lib DeveloperTools where globs := #[`DeveloperTools.*]

lean_lib Executables where globs := #[`Executables.*]

lean_exe «dump-syntax-tree» where root := `DeveloperTools.DumpSyntaxTree

lean_exe heron where
  root := `Executables.LakeLintDriver
  supportInterpreter := true

lean_exe «heron-scan» where
  root := `Executables.StandaloneScan
  supportInterpreter := true

lean_exe «heron-language-server» where root := `Executables.SecondLanguageServer

target plugin : Dynlib := do
  let some heron ← findLeanLib? `Heron
    | error "library `Heron` not found"
  heron.shared.fetch
