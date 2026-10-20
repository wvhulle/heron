import FixReporting.FixReportRendering
import FixReporting.StandaloneScan.SharedEnvironment
import DevExecutables.SelfLint.PositionalSyntaxAccess
import DevExecutables.SelfLint.SyntaxKindOrAtomInspection
import DevExecutables.SelfLint.SyntheticSyntaxConstruction
import DevExecutables.SelfLint.SourcePositionInRule
import DevExecutables.SelfLint.SourceTextInRule

/-!
# `heron-self-lint` — Heron's own rules, checked against their implementations

Runs the self-lint checks named in `selfLints` over every rule file in `Heron/Check`,
`Heron/Refactor` and `DevExecutables/SelfLint`, prints the findings like `heron-scan` does, and
exits with status 1 when there are any. Requires the library to be built.

    lake build && lake exe heron-self-lint
-/

open FixReporting Lean

def selfLints : Array Name := #[
  `positionalSyntaxAccess, `syntaxKindOrAtomInspection, `syntheticSyntaxConstruction,
  `sourcePositionInRule, `sourceTextInRule]

def ruleDirectories : Array System.FilePath :=
  #["Heron" / "Check", "Heron" / "Refactor", "DevExecutables" / "SelfLint"]

def ruleFiles : IO (Array String) := do
  let mut files := #[]
  for dir in ruleDirectories do
    for entry in ← dir.readDir do
      if entry.path.extension == some "lean" then files := files.push entry.path.toString
  return files.qsort (· < ·)

unsafe def main (_ : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let checks ← match selectChecks (← Heron.heronRuleRegistry.get) selfLints with
    | .error e => do IO.eprintln s!"heron-self-lint: {e}"; return 1
    | .ok checks => pure checks
  let reports ← lintShared (all := false) (useCache := false) checks 16 (← ruleFiles)
  let pal : Palette := { on := ← decideColor none false }
  let _ ← emit reports pal (json := false) (apply := false) (fix := false)
  let total := (reports.map (·.fixes.size)).sum
  if total == 0 then return 0
  (← IO.getStdout).flush
  IO.eprintln s!"heron-self-lint: {total} finding(s) in rule implementations; see \"Writing a rule\" in CONTRIBUTING.md"
  return 1
