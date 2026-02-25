import Heron.AssertSuggests
import Heron.AssertEdits
import Heron.AssertNoSuggests
import Heron.Diagnostic

open Lean Elab Command Meta

namespace Heron.Rules

class Rule (α : Type) where
  /-- Rule name, used to derive the linter option `linter.<name>`. -/
  ruleName : Name
  /-- Detect violations, returning typed fix data. -/
  detect : Syntax → CommandElabM (Array α)
  /-- Syntax node to underline in the diagnostic. -/
  diagnosticNode : α → Syntax
  /-- Hint message shown alongside the suggestion widget. -/
  hintMessage : MessageData
  /-- Main diagnostic message shown as the linter warning. -/
  diagnosticMessage : MessageData
  /-- Replacement text for the fix. -/
  replacementText : α → String
  /-- Syntax node whose range is replaced by `replacementText`. -/
  replacementNode : α → Syntax
  /-- Diagnostic severity. -/
  severity : MessageSeverity
  /-- LSP diagnostic tags (e.g. unnecessary, deprecated). -/
  diagnosticTags : Array Lsp.DiagnosticTag := #[]

def Rule.option [Rule α] : Lean.Option Bool :=
  { name := `linter ++ Rule.ruleName (α := α), defValue := false }

def Rule.toLinter [Rule α] : Linter where
  run :=
    withSetOptionIn fun stx => do
      let opt := Rule.option (α := α)
      unless opt.get (← getOptions) do return
      if Heron.isReelaborating (← getOptions) then return
      for fixData in ← Rule.detect (α := α) stx do
        Heron.emitDiagnostic
          (Rule.diagnosticNode (α := α) fixData)
          (Rule.replacementNode (α := α) fixData)
          (Rule.severity (α := α))
          (Rule.diagnosticTags (α := α))
          (Rule.ruleName (α := α))
          opt.name
          (Rule.diagnosticMessage (α := α))
          (Rule.hintMessage (α := α))
          (Rule.replacementText (α := α) fixData)

def Rule.initOption [Rule α] : IO Unit :=
  Lean.registerOption (`linter ++ Rule.ruleName (α := α))
    { defValue := .ofBool false
      descr := s! "Enable the {Rule.ruleName (α := α)} linter rule."
      name := `linter }

def Rule.addLinter [Rule α] : IO Unit :=
  lintersRef.modify (·.push (Rule.toLinter (α := α)))

end Heron.Rules
