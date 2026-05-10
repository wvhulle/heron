module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure SyntaxKindCheckMatch where
  fullStx : TSyntax `term

private meta instance : Check SyntaxKindCheckMatch where
  name := `syntaxKindCheck
  kinds := #[``«term_==_», ``«term_!=_», ``Term.app]
  severity := .information
  category := .style
  detect := fun stx => pure <|
    match stx with
    | `(($_:term).getKind == $_) => #[{ fullStx := ⟨stx⟩ }]
    | `(($_:term).getKind != $_) => #[{ fullStx := ⟨stx⟩ }]
    | `(($_:term).isOfKind $_) => #[{ fullStx := ⟨stx⟩ }]
    | _ => #[]
  message := fun _ => m!"Use antiquotation pattern matching instead of comparing `Syntax.getKind`"
  emphasize := fun m => m.fullStx
  reference := some
    { topic := "Syntax pattern matching"
      url := "https://leanprover-community.github.io/lean4-metaprogramming-book/main/06_macros.html" }
  explanation := fun _ =>
    m!"Comparing a node's kind by name (e.g. `stx.getKind == ``Term.doLet`) hard-codes the parser's \
       internal layout. When upstream Lean shifts that layout — by inserting a new optional child, \
       for example — the check still type-checks but silently stops matching. Pattern-matching with \
       `` `(...) `` antiquotations is checked at compile time and adapts to parser changes."
  replacements := fun _ => return #[]

meta initialize Check.register (α := SyntaxKindCheckMatch)
