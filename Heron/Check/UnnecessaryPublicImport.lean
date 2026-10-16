module

public meta import Heron.Check
public meta import Heron.ImportAnalysis

open Lean Elab Command Heron

private structure UnnecessaryPublicImportMatch where
  importStx : Syntax
  publicKw : Syntax
  moduleName : Name

private meta def detectUnnecessaryPublicImports (stx : Syntax) :
    CommandElabM (Array UnnecessaryPublicImportMatch) := do
  let analyses ← ImportAnalysis.analyzeImports stx
  return analyses.filterMap fun a => do
    guard (a.isUsed && a.imp.isExported && !a.needsExported)
    let `(Lean.Parser.Module.import| $[public%$pubTk?]? $[meta%$_]? import $[all%$_]? $_) :=
      a.importStx | none
    let publicKw ← pubTk?
    some { importStx := a.importStx, publicKw, moduleName := a.imp.module }

private meta instance : Check UnnecessaryPublicImportMatch where
  name := `unnecessaryPublicImport
  kinds := #[]
  severity := .warning
  category := .simplification
  detect := detectUnnecessaryPublicImports
  message := fun m => m!"`public` qualifier on import `{m.moduleName}` is unnecessary"
  emphasize := fun m => m.publicKw
  tags := #[.unnecessary]
  explanation := fun _ =>
    m!"This import does not need to be re-exported. It can be a plain `import`."
  replacements := fun m => do
    return #[{
      emphasizedSyntax := m.publicKw
      oldSyntax := m.publicKw
      newSyntax := .missing
      inlineViolationLabel := m!"unnecessary public"
    }]

meta initialize Check.register (α := UnnecessaryPublicImportMatch)
