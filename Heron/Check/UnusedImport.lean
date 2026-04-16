module

public meta import Heron.Check
public meta import Heron.ImportAnalysis

open Lean Elab Command Heron

private structure UnusedImportMatch where
  importStx : Syntax
  moduleName : Name

private meta def detectUnusedImports (stx : Syntax) : CommandElabM (Array UnusedImportMatch) := do
  let analyses ← ImportAnalysis.analyzeImports stx
  return analyses.filterMap fun a =>
    if !a.isUsed then
      some { importStx := a.importStx, moduleName := a.imp.module }
    else
      none

@[check_rule] private meta instance : Check UnusedImportMatch where
  name := `unusedImport
  severity := .warning
  category := .simplification
  detect := detectUnusedImports
  message := fun m => m!"Unused import `{m.moduleName}`"
  emphasize := fun m => m.importStx
  tags := #[.unnecessary]
  explanation := fun m =>
    m!"This import does not contribute any constants or elaboration dependencies used in this file."
  replacements := fun m => do
    return #[{
      emphasizedSyntax := m.importStx
      oldSyntax := m.importStx
      newSyntax := .missing
      inlineViolationLabel := m!"unused import"
    }]
