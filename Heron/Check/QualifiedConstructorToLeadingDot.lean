module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

set_option linter.sourcePositionInRule false
set_option linter.syntaxKindComparisonToQuotationPattern false
set_option linter.syntaxKindOrAtomInspection false
set_option linter.syntheticSyntaxConstruction false

open Lean Elab Command Meta Parser Heron

private structure QualifiedConstructorToLeadingDotMatch where
  ident : Syntax
  constructorField : Name

private meta partial def qualifiedIdents (stx : Syntax) : Array Syntax :=
  if stx.isIdent then
    if stx.getId.getNumParts ≥ 2 then #[stx] else #[]
  else if stx.getKind == ``Term.explicit || stx.getKind == ``Command.declId then #[]
  else stx.getArgs.flatMap qualifiedIdents

private meta def writtenAsSuffixOf (written resolved : Name) : Bool :=
  let writtenParts := written.components
  resolved.components.drop (resolved.getNumParts - writtenParts.length) == writtenParts

private meta def constructorFieldOf? (env : Environment) (written : Name) (ti : TermInfo) :
    MetaM (Option Name) := do
  let some ctor := (← instantiateMVars ti.expr).getAppFn.constName? | return none
  let some (.ctorInfo _) := env.find? ctor | return none
  unless writtenAsSuffixOf written ctor do return none
  return ctor.componentsRev.head?

private meta def qualifiedConstructorField? (ident : Syntax) : CommandElabM (Option Name) := do
  let env ← getEnv
  let some pos := ident.getPos? | return none
  let trees ← collectInfoTrees ident
  let infosAtIdent := (trees.flatMap collectTermInfos).filter fun (_, ti) => ti.stx.getPos? == some pos
  infosAtIdent.findSomeM? fun (ci, ti) => runInfoMetaM ci ti.lctx (constructorFieldOf? env ident.getId ti)

private meta def dottedConstructor (field : Name) : CommandElabM (TSyntax `term) :=
  `(.$(mkIdent field):ident)

private meta def withLeadingDots (cmd : Syntax) (candidates : Array QualifiedConstructorToLeadingDotMatch) :
    CommandElabM Syntax :=
  candidates.foldlM (init := cmd) fun rewritten candidate => do
    return replaceSourceNode rewritten candidate.ident (← dottedConstructor candidate.constructorField)

private meta def detectQualifiedConstructors (cmd : Syntax) :
    CommandElabM (Array QualifiedConstructorToLeadingDotMatch) := do
  let candidates ← (qualifiedIdents cmd).filterMapM fun ident => do
    let some constructorField ← qualifiedConstructorField? ident | return none
    return some { ident, constructorField }
  if candidates.isEmpty then return #[]
  if ← elaboratesWithoutErrorsInProbeNamespace (← withLeadingDots cmd candidates) then return candidates
  candidates.filterM fun candidate => do
    elaboratesWithoutErrorsInProbeNamespace (← withLeadingDots cmd #[candidate])

private meta instance : Check QualifiedConstructorToLeadingDotMatch where
  name := `qualifiedConstructorToLeadingDot
  description := "Suggests `.leaf` instead of `BinTree.leaf` where the expected type is known."
  kinds := #[]
  wholeCommand := true
  severity := .information
  category := .style
  detect := detectQualifiedConstructors
  message := fun m => m!"Use `.{m.constructorField}` instead of the fully qualified constructor"
  emphasize := fun m => m.ident
  sources := #[.functionalProgrammingInLean "Leading dot notation"
    "Monads/Additional-Conveniences/#leading-dot-notation"]
  explanation := fun _ =>
    m!"When the expected type is known, Lean resolves `.c` in that type's namespace, so the \
       constructor can be written without repeating the type name. This makes pattern matches and \
       constructor applications shorter, at the cost of being less explicit when the code is read \
       outside an editor. The hint only appears where the declaration still elaborates with the \
       leading dot."
  replacements := some fun m => do
    return #[{
      emphasizedSyntax := m.ident
      oldSyntax := m.ident
      newSyntax := ← dottedConstructor m.constructorField
      inlineViolationLabel := m!"leading dot"
    }]

register_check QualifiedConstructorToLeadingDotMatch
