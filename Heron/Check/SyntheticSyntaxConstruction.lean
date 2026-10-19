module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Heron

private structure SyntheticSyntaxConstructionMatch where
  site : Syntax

private meta def syntaxConstructors : Array Name :=
  #[``Lean.mkAtom, ``Lean.mkIdent, ``Lean.mkIdentFrom, ``Lean.mkNullNode, ``Lean.mkNode,
    ``Lean.Syntax.mkNumLit, ``Lean.Syntax.mkStrLit, ``Lean.Syntax.mkLit, ``Lean.Syntax.ofRange,
    ``Lean.Syntax.node, ``Lean.Syntax.atom, ``Lean.Syntax.ident]

private meta instance : Check SyntheticSyntaxConstructionMatch where
  name := `syntheticSyntaxConstruction
  description := "Flags syntax assembled from atoms, identifiers or raw nodes instead of a quotation."
  kinds := #[]
  wholeCommand := true
  severity := .warning
  category := .style
  detect := fun cmd => do
    let sites ← originalCallSitesOf cmd fun e => syntaxConstructors.any e.getAppFn.isConstOf
    return sites.map ({ site := · })
  message := fun _ => m!"Build syntax with a quotation instead of assembling nodes, atoms or identifiers by hand"
  emphasize := fun m => m.site
  sources := #[.metaprogrammingInLean "Syntax" "05_syntax.html"]
  explanation := fun _ =>
    m!"`mkAtom`, `mkIdent`, `mkNode` and the `Syntax` constructors produce trees that nothing \
       checks against the grammar, and identifiers made from strings are not hygienic. A \
       `` `(...) `` quotation builds the same syntax from source text that is parsed when the \
       rule is compiled; use `quote` for literals and antiquotations for the matched pieces."

register_check SyntheticSyntaxConstructionMatch
