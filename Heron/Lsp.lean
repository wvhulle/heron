module

public meta import Heron.Rule
public meta import Lean.PrettyPrinter

public section

open Lean Elab Command Meta

namespace Heron

/-- Result of running a rule against a single command for testing. -/
structure RunResult where
  /-- How many matches `Rule.detect` produced. Zero means the rule did not fire. -/
  matchCount : Nat
  /-- Text edits derived from those matches' `Rule.replacements`. May be empty
  even when `matchCount > 0` for warning-only rules with no automatic fix. -/
  edits : Array Lsp.TextEdit

/-- Type-erased rule runner: given syntax, produces a detection count and
LSP `TextEdit`s via `Rule.detect` + `Rule.replacements` + `Replacement.toTextEdit?`. -/
meta abbrev TestRunner :=
  Syntax → CommandElabM RunResult

/-- Registry of rule runners, keyed by rule name. Used by test macros to
invoke rules directly without going through the linter/diagnostic path. -/
meta initialize testRunnerRegistry : IO.Ref (Std.HashMap Name TestRunner) ←
  IO.mkRef { }

/-- Convert a single replacement to an LSP `TextEdit`, using Lean's pretty printer
to format the replacement text. Falls back to `reprint` if formatting fails. -/
meta def Replacement.toTextEdit (r : Replacement) (fileMap : FileMap) : CoreM (Option Lsp.TextEdit) := do
  let some range := r.oldSyntax.getRange? | return none
  let lspRange := fileMap.utf8RangeToLspRange range
  if r.newSyntax.isMissing then
    return some { range := lspRange, newText := "" }
  let newText ← try
    pure (← PrettyPrinter.ppCategory r.category r.newSyntax).pretty
  catch _ =>
    let some text := r.newSyntax.reprint | return none
    pure text.trimAscii.toString
  return some { range := lspRange, newText }

/-- Build a type-erased test runner for a `Rule` instance. -/
meta def buildTestRunner [Rule α] : TestRunner := fun stx => do
  let fileMap ← getFileMap
  let results ← Rule.detectAll (α := α) stx
  let edits ← results.flatMapM fun m => do
    let repls ← Rule.replacements (α := α) m
    repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
  return { matchCount := results.size, edits }

end Heron
