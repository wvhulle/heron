module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Heron

private structure SyntaxKindOrAtomInspectionMatch where
  site : Syntax

private meta def kindAndAtomInspectors : Array Name :=
  #[``Lean.Syntax.getKind, ``Lean.Syntax.isOfKind, ``Lean.Syntax.getAtomVal, ``Lean.Syntax.getHead?]

private meta instance : Check SyntaxKindOrAtomInspectionMatch where
  name := `syntaxKindOrAtomInspection
  description := "Flags `getKind`, `isOfKind` and `getAtomVal` where a quotation pattern would match the node."
  kinds := #[``Lean.Parser.Command.declaration]
  severity := .warning
  category := .style
  detect := fun cmd => do
    let sites ← originalCallSitesOf cmd fun e => kindAndAtomInspectors.any e.getAppFn.isConstOf
    return sites.map ({ site := · })
  message := fun _ => m!"Match the node with a quotation pattern instead of inspecting its kind or atom"
  emphasize := fun m => m.site
  sources := #[.metaprogrammingInLean "Matching on syntax" "05_syntax.html#matching-on-syntax"]
  explanation := fun _ =>
    m!"Comparing `getKind` or `getAtomVal` against a literal re-implements what a `` `(...) `` \
       pattern already does, without the compile-time check that the shape exists. Write the \
       shape you expect as a quotation and let the pattern fail to match otherwise."

register_check SyntaxKindOrAtomInspectionMatch
