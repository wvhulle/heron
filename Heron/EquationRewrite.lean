module

public meta import Heron.Check
public meta import Heron.Monad

public section

open Lean Elab Command

namespace Heron

structure EquationRewriteMatch where
  node : Syntax
  replacement : Syntax

structure EquationRewrite where
  name : Name
  description : String
  equation : Name
  rightToLeft : Bool := false
  message : MessageData
  label : MessageData
  explanation : MessageData := m!""
  severity : MessageSeverity := .information
  category : Category := .simplification
  tags : Array Lsp.DiagnosticTag := #[]
  sources : Array Source := #[]

private meta def detectEquationSide (equation : Name) (rightToLeft : Bool) (node : Syntax) :
    CommandElabM (Array EquationRewriteMatch) := do
  let some replacement ← rewriteByEquationAt? node equation rightToLeft | return #[]
  unless ← rewriteElaborates node replacement do return #[]
  let replacement : Term := ⟨← liftCoreM <| PrettyPrinter.parenthesizeTerm replacement⟩
  let replacement ← if ← needsParenthesesAt node replacement then `(($replacement)) else pure replacement
  return #[{ node, replacement }]

@[reducible] meta def rewriteByEquation (spec : EquationRewrite) : Check EquationRewriteMatch where
  name := spec.name
  description := spec.description
  kinds := #[``Parser.Term.app, ``Parser.Term.pipeProj, ``Parser.Term.proj]
  consumesSubtree := true
  detect := detectEquationSide spec.equation spec.rightToLeft
  message := fun _ => spec.message
  explanation := fun _ => spec.explanation
  emphasize := (·.node)
  severity := spec.severity
  category := spec.category
  tags := spec.tags
  sources := spec.sources
  replacements := some fun found => return #[{
    emphasizedSyntax := found.node
    oldSyntax := found.node
    newSyntax := found.replacement
    inlineViolationLabel := spec.label }]

end Heron
