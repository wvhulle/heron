module

public meta import Heron.Check
meta import Heron.Register
public meta import DeveloperTools.OriginalCallSites

open Lean Elab Command Heron

private structure SourcePositionInRuleMatch where
  site : Syntax

private meta def positionReaders : Array Name :=
  #[``Lean.Syntax.getPos?, ``Lean.Syntax.getTailPos?, ``Lean.Syntax.getRange?,
    ``Lean.FileMap.toPosition, ``Lean.FileMap.ofPosition]

private meta instance : Check SourcePositionInRuleMatch where
  name := `sourcePositionInRule
  description := "Flags source positions (`getPos?`, `getRange?`) read inside a rule."
  kinds := #[``Lean.Parser.Command.declaration]
  severity := .warning
  category := .style
  detect := fun cmd => do
    let sites ← originalCallSitesOf cmd fun e => positionReaders.any e.getAppFn.isConstOf
    return sites.map ({ site := · })
  message := fun _ => m!"Compare syntax structurally instead of reading source positions"
  emphasize := fun m => m.site
  sources := #[.metaprogrammingInLean "Syntax" "05_syntax.html"]
  explanation := fun _ =>
    m!"Positions say where code was written, not what it is. Deciding order, adjacency or \
       containment from `getPos?` or `getRange?` breaks on reformatting and on synthetic syntax. \
       Match the enclosing node with a quotation that names both parts, and report with \
       `emphasize`; only the framework turns syntax into positions."

register_check SourcePositionInRuleMatch
