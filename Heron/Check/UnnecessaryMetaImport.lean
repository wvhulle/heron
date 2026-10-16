module

public meta import Heron.Check
public meta import Heron.ImportAnalysis
meta import Heron.Register

open Lean Elab Command Heron

private structure UnnecessaryMetaImportMatch where
  importStx : Syntax
  metaKw : Syntax
  moduleName : Name

private meta def detectUnnecessaryMetaImports (stx : Syntax) :
    CommandElabM (Array UnnecessaryMetaImportMatch) := do
  let analyses ← ImportAnalysis.analyzeImports stx
  return analyses.filterMap fun a => do
    guard (a.isUsed && a.imp.isMeta && !a.needsMeta)
    let `(Lean.Parser.Module.import| $[public%$_]? $[meta%$metaTk?]? import $[all%$_]? $_) :=
      a.importStx | none
    let metaKw ← metaTk?
    some { importStx := a.importStx, metaKw, moduleName := a.imp.module }

private meta instance : Check UnnecessaryMetaImportMatch where
  name := `unnecessaryMetaImport
  description := "Suggests a plain `import` where a `meta import` provides nothing the file uses at compile time."
  kinds := #[``Lean.Parser.Command.eoi]
  severity := .warning
  category := .simplification
  detect := detectUnnecessaryMetaImports
  message := fun m => m!"`meta` qualifier on import `{m.moduleName}` is unnecessary"
  emphasize := fun m => m.metaKw
  tags := #[.unnecessary]
  explanation := fun _ =>
    m!"This import does not need to provide IR/compilation data. It can be a plain `import`."
  replacements := some fun m => do
    return #[{
      emphasizedSyntax := m.metaKw
      oldSyntax := m.metaKw
      newSyntax := .missing
      inlineViolationLabel := m!"unnecessary meta"
    }]

register_check UnnecessaryMetaImportMatch
