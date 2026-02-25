import Heron.AssertSuggests
import Heron.AssertEdits
import Heron.AssertNoSuggests
import Heron.Diagnostic
import Heron.Refactor

open Lean Elab Command Meta

namespace Heron.Rules

class Rule (α : Type) where
  /-- Rule name, used to derive the linter option `linter.<name>`. -/
  ruleName : Name
  /-- Detect violations, returning typed fix data. -/
  detect : Syntax → CommandElabM (Array α)
  /-- Syntax node to underline in the diagnostic (Lint) or anchor the code action (Refactor). -/
  diagnosticNode : α → Syntax
  /-- Hint message shown alongside the suggestion widget. -/
  hintMessage : MessageData
  /-- Main diagnostic message shown as the linter warning. -/
  diagnosticMessage : MessageData
  /-- Replacement text for the fix. -/
  replacementText : α → String
  /-- Syntax node whose range is replaced by `replacementText`. -/
  replacementNode : α → Syntax

class Lint (α : Type) extends Rule α where
  /-- Diagnostic severity. -/
  severity : MessageSeverity
  /-- LSP diagnostic tags (e.g. unnecessary, deprecated). -/
  diagnosticTags : Array Lsp.DiagnosticTag := #[]

class Refactor (α : Type) extends Rule α

def Rule.option [Rule α] : Lean.Option Bool :=
  { name := `linter ++ Rule.ruleName (α := α), defValue := false }

def Rule.initOption [Rule α] : IO Unit :=
  Lean.registerOption (`linter ++ Rule.ruleName (α := α))
    { defValue := .ofBool false
      descr := s! "Enable the {Rule.ruleName (α := α)} linter rule."
      name := `linter }

def Lint.toLinter [Lint α] : Linter where
  run :=
    withSetOptionIn fun stx => do
      let opt := Rule.option (α := α)
      unless opt.get (← getOptions) do return
      if Heron.isReelaborating (← getOptions) then return
      for fixData in ← Rule.detect (α := α) stx do
        Heron.emitDiagnostic
          (Rule.diagnosticNode (α := α) fixData)
          (Rule.replacementNode (α := α) fixData)
          (Lint.severity (α := α))
          (Lint.diagnosticTags (α := α))
          (Rule.ruleName (α := α))
          opt.name
          (Rule.diagnosticMessage (α := α))
          (Rule.hintMessage (α := α))
          (Rule.replacementText (α := α) fixData)

def Lint.addLinter [Lint α] : IO Unit :=
  lintersRef.modify (·.push (Lint.toLinter (α := α)))

def Refactor.toLinter [Refactor α] : Linter where
  run :=
    withSetOptionIn fun stx => do
      let opt := Rule.option (α := α)
      unless opt.get (← getOptions) do return
      if Heron.isReelaborating (← getOptions) then return
      for fixData in ← Rule.detect (α := α) stx do
        Heron.emitSuggestion
          (Rule.diagnosticNode (α := α) fixData)
          (Rule.replacementNode (α := α) fixData)
          (Rule.hintMessage (α := α))
          (Rule.replacementText (α := α) fixData)

def Refactor.addLinter [Refactor α] : IO Unit :=
  lintersRef.modify (·.push (Refactor.toLinter (α := α)))

end Heron.Rules
