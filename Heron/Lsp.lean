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

/-- Build a `DiagnosticRelatedInformation` entry for `l`, anchoring it at
`l.span`'s LSP range in the file identified by `uri`. Returns `none` if the
span has no source range. -/
meta def Label.toRelatedInformation (l : Label) (fileMap : FileMap) (uri : Lsp.DocumentUri) :
    CommandElabM (Option Lsp.DiagnosticRelatedInformation) := do
  let some range := l.span.getRange? | return none
  let lspRange := fileMap.utf8RangeToLspRange range
  let formatted ← (← addMessageContext l.text).format
  return some { location := { uri, range := lspRange }, message := formatted.pretty }

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

/-- Collect `DiagnosticRelatedInformation` entries for one match: one per
replacement (using `Replacement.toLabel`), plus any extra label-only entries
from `Rule.labels`. -/
meta def collectRelatedInformation [Rule α] (m : α) (repls : Array Replacement)
    (fileMap : FileMap) (uri : Lsp.DocumentUri) :
    CommandElabM (Array Lsp.DiagnosticRelatedInformation) := do
  let fromRepls ← repls.filterMapM fun r => r.toLabel.toRelatedInformation fileMap uri
  let extras ← Rule.labels (α := α) m
  let fromExtras ← extras.filterMapM fun l => l.toRelatedInformation fileMap uri
  return fromRepls ++ fromExtras

/-- Build a type-erased test runner for a `Rule` instance. -/
meta def buildTestRunner [Rule α] : TestRunner := fun stx => do
  let fileMap ← getFileMap
  let results ← Rule.detectAll (α := α) stx
  let edits ← results.flatMapM fun m => do
    let repls ← Rule.replacements (α := α) m
    repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
  return { matchCount := results.size, edits }

end Heron
