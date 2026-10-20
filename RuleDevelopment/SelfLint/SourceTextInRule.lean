module

public meta import Heron.Check
meta import Heron.Register
public meta import RuleDevelopment.SelfLint.OriginalCallSites

open Lean Elab Command Heron

private structure SourceTextInRuleMatch where
  site : Syntax

private meta def textReaders : Array Name :=
  #[``Lean.Syntax.reprint, ``Lean.Syntax.getSubstring?, ``Lean.Name.toString,
    ``String.splitOn, ``String.trimAscii, ``String.trimAsciiStart, ``String.trimAsciiEnd,
    ``String.startsWith, ``String.endsWith]

private meta instance : Check SourceTextInRuleMatch where
  name := `sourceTextInRule
  description := "Flags syntax or names turned back into text (`reprint`, `Name.toString`, string splitting) inside a rule."
  kinds := #[``Lean.Parser.Command.declaration]
  severity := .warning
  category := .style
  detect := fun cmd => do
    let sites ← originalCallSitesOf cmd fun e => textReaders.any e.getAppFn.isConstOf
    return sites.map ({ site := · })
  message := fun _ => m!"Work on syntax and names, not on their text"
  emphasize := fun m => m.site
  sources := #[.metaprogrammingInLean "Syntax" "05_syntax.html"]
  explanation := fun _ =>
    m!"Printing syntax or a name back to text and searching that text throws away the structure \
       Lean already parsed, and depends on spelling, whitespace and namespaces. Match the \
       syntax with a quotation, compare `Name`s as names, and read types from the info tree."

register_check SourceTextInRuleMatch
