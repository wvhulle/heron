module

public meta import Heron.Check
meta import Heron.Register
public meta import DevExecutables.SelfLint.OriginalCallSites

open Lean Elab Command Heron

private structure SyntheticSyntaxConstructionMatch where
  site : Syntax

private meta def syntaxConstructors : Array Name :=
  #[``Lean.mkAtom, ``Lean.mkNode,
    ``Lean.Syntax.mkNumLit, ``Lean.Syntax.mkStrLit, ``Lean.Syntax.mkLit, ``Lean.Syntax.ofRange,
    ``Lean.Syntax.node, ``Lean.Syntax.atom, ``Lean.Syntax.ident]

private meta def identifierConstructors : Array Name :=
  #[``Lean.mkIdent, ``Lean.mkIdentFrom, ``Lean.mkCIdent, ``Lean.mkCIdentFrom]

private meta def isNameLiteral (e : Expr) : Bool :=
  !e.hasFVar && !e.hasMVar && e.getAppFn.constName?.any (·.getPrefix == ``Lean.Name)

private meta def identifierFromLiteralName (e : Expr) : Bool :=
  identifierConstructors.any e.getAppFn.isConstOf && e.getAppArgs.any isNameLiteral

private meta instance : Check SyntheticSyntaxConstructionMatch where
  name := `syntheticSyntaxConstruction
  description := "Flags syntax assembled from atoms or raw nodes, and identifiers made from a literal name, instead of a quotation; `mkNullNode` over source nodes, used as a span, is allowed."
  kinds := #[``Lean.Parser.Command.declaration]
  severity := .warning
  category := .style
  detect := fun cmd => do
    let constructed ← originalCallSitesOf cmd fun e => syntaxConstructors.any e.getAppFn.isConstOf
    let literalIdentifiers ← originalApplicationsOf cmd identifierFromLiteralName
    return (constructed ++ literalIdentifiers).map ({ site := · })
  message := fun _ => m!"Build syntax with a quotation instead of assembling nodes, atoms or identifiers by hand"
  emphasize := fun m => m.site
  sources := #[.metaprogrammingInLean "Syntax" "05_syntax.html"]
  explanation := fun _ =>
    m!"`mkAtom`, `mkNode` and the `Syntax` constructors produce trees that nothing checks against \
       the grammar. A `` `(...) `` quotation builds the same syntax from source text that is \
       parsed when the rule is compiled; use `quote` for literals and antiquotations for the \
       matched pieces. An identifier whose name is fixed in the rule is written in a quotation \
       under `set_option hygiene false in`, as Lean core does for code-action text; `mkIdent` is \
       for names that come out of elaboration, such as a resolved constructor."

register_check SyntheticSyntaxConstructionMatch
