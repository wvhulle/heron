module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Meta Parser Heron

private structure QualifiedConstructorToLeadingDotMatch where
  ident : Ident
  constructorField : Name

private structure ConstructorReference where
  field : Name
  expectedTypeNamesItsInductive : Bool

private meta def constructorReference? (ti : TermInfo) : MetaM (Option ConstructorReference) := do
  let some ctor := (← instantiateMVars ti.expr).getAppFn.constName? | return none
  let some (.ctorInfo info) := (← getEnv).find? ctor | return none
  let .str _ field := ctor | return none
  let expectedTypeNamesItsInductive ← match ti.expectedType? with
    | some expected => pure ((← whnfR (← instantiateMVars expected)).getAppFn.isConstOf info.induct)
    | none => pure true
  return some { field := .mkSimple field, expectedTypeNamesItsInductive }

private meta def dottedConstructor (field : Name) : CommandElabM Term :=
  `(.$(mkIdent field):ident)

private meta def detectQualifiedConstructor (site : Syntax) :
    CommandElabM (Array QualifiedConstructorToLeadingDotMatch) := do
  let `($ident:ident) := site | return #[]
  unless ident.getId.getNumParts ≥ 2 do return #[]
  let references := (← runMetaMForEachExactTermInfo ident constructorReference?).filterMap id
  let some reference := references[0]? | return #[]
  unless references.all (·.expectedTypeNamesItsInductive) do return #[]
  unless ← rewriteElaborates ident (← dottedConstructor reference.field) do return #[]
  return #[{ ident, constructorField := reference.field }]

private meta instance : Check QualifiedConstructorToLeadingDotMatch where
  name := `qualifiedConstructorToLeadingDot
  description := "Suggests `.leaf` instead of `BinTree.leaf` where the expected type is known."
  kinds := #[identKind]
  severity := .information
  category := .style
  detect := detectQualifiedConstructor
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
