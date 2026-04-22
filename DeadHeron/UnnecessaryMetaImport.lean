module

public meta import Heron.Check
public meta import DeadHeron.ImportAnalysis

open Lean Elab Command Heron

private structure UnnecessaryMetaImportMatch where
  importStx : Syntax
  metaKw : Syntax
  moduleName : Name

private meta def detectUnnecessaryMetaImports (stx : Syntax) :
    CommandElabM (Array UnnecessaryMetaImportMatch) := do
  let analyses ← ImportAnalysis.analyzeImports stx
  return analyses.filterMap fun a =>
    if a.isUsed && a.imp.isMeta && !a.needsMeta then
      -- Extract the `meta` keyword syntax from the import syntax node
      -- Import syntax: `$[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id`
      let metaKw := a.importStx[1]![0]!
      some { importStx := a.importStx, metaKw, moduleName := a.imp.module }
    else
      none

private meta instance : Check UnnecessaryMetaImportMatch where
  name := `unnecessaryMetaImport
  severity := .warning
  category := .simplification
  detect := detectUnnecessaryMetaImports
  message := fun m => m!"`meta` qualifier on import `{m.moduleName}` is unnecessary"
  emphasize := fun m => m.metaKw
  tags := #[.unnecessary]
  explanation := fun _ =>
    m!"This import does not need to provide IR/compilation data. It can be a plain `import`."
  replacements := fun m => do
    return #[{
      emphasizedSyntax := m.metaKw
      oldSyntax := m.metaKw
      newSyntax := .missing
      inlineViolationLabel := m!"unnecessary meta"
    }]

meta initialize Check.register (α := UnnecessaryMetaImportMatch)
