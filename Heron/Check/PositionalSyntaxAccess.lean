module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Heron

private structure PositionalSyntaxAccessMatch where
  site : Syntax

private meta instance : Check PositionalSyntaxAccessMatch where
  name := `positionalSyntaxAccess
  description := "Flags syntax children read by position (`getArg`, `stx[i]`) or hand-written walks in a rule."
  kinds := #[``Lean.Parser.Command.declaration]
  severity := .warning
  category := .style
  detect := fun cmd => do
    let sites ← originalCallSitesOf cmd isPositionalSyntaxAccess
    return sites.map ({ site := · })
  message := fun _ => m!"Match syntax children with a quotation pattern instead of reading them by position"
  emphasize := fun m => m.site
  sources := #[.metaprogrammingInLean "Matching on syntax" "05_syntax.html#matching-on-syntax"]
  explanation := fun _ =>
    m!"`getArg`, `getArgs`, `stx[i]` and hand-written walks over the children depend on the \
       parser's layout and break silently when it changes. A `` `(...) `` pattern with \
       antiquotations binds the children by name and is checked when the rule is compiled."

register_check PositionalSyntaxAccessMatch
