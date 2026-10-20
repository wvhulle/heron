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

private meta def detectEquationSides (equation : Name) (rightToLeft : Bool) (command : Syntax) :
    CommandElabM (Array EquationRewriteMatch) := do
  (← rewritesByEquationIn command equation rightToLeft).mapM fun (node, replacement) => do
    let replacement : Term := ⟨← liftCoreM <| PrettyPrinter.parenthesizeTerm replacement⟩
    let replacement ← if ← needsParenthesesAt node replacement then `(($replacement)) else pure replacement
    return { node, replacement }

@[reducible] meta def rewriteByEquation (spec : EquationRewrite) : Check EquationRewriteMatch where
  name := spec.name
  description := spec.description
  kinds := #[`command]
  consumesSubtree := true
  detect := detectEquationSides spec.equation spec.rightToLeft
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
