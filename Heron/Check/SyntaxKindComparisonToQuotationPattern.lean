module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure SyntaxKindComparisonToQuotationPatternMatch where
  fullStx : TSyntax `term

private meta def isGetKindAccess : Syntax → Bool
  | `(($_:term).getKind) => true
  | `($x:ident) => isDottedAccess `getKind x.getId
  | _ => false

private meta def isIsOfKindCall : Syntax → Bool
  | `(($_:term).isOfKind $_) => true
  | `($fn:ident $_) => isDottedAccess `isOfKind fn.getId
  | _ => false

private meta def kindQuery? : Syntax → Option (Syntax × Name)
  | `($lhs == $_) | `($lhs != $_) =>
    if isGetKindAccess lhs then some (lhs, ``Lean.Syntax.getKind) else none
  | stx => if isIsOfKindCall stx then some (stx, ``Lean.Syntax.isOfKind) else none

private meta instance : Check SyntaxKindComparisonToQuotationPatternMatch where
  name := `syntaxKindComparisonToQuotationPattern
  kinds := #[``«term_==_», ``«term_!=_», ``Term.app]
  severity := .information
  category := .style
  detect := fun stx => do
    let some (query, syntaxMethod) := kindQuery? stx | return #[]
    unless ← elaboratesToApplicationOf query syntaxMethod do return #[]
    return #[{ fullStx := ⟨stx⟩ }]
  message := fun _ => m!"Use antiquotation pattern matching instead of comparing `Syntax.getKind`"
  emphasize := fun m => m.fullStx
  reference := some
    { topic := "Syntax pattern matching"
      url := "https://leanprover-community.github.io/lean4-metaprogramming-book/main/06_macros.html" }
  explanation := fun _ =>
    m!"Comparing a node's kind by name (e.g. `stx.getKind == ``Term.doLet`) only tells you which \
       parser produced the node; it binds none of its children. Code that follows such a check \
       usually reaches for positional `getArg` indexing, which silently breaks when upstream Lean \
       changes the parser's layout. Pattern-matching with `` `(...) `` antiquotations checks the \
       kind and binds the children by name in one step, and is checked at compile time."
  replacements := fun _ => return #[]

meta initialize Check.register (α := SyntaxKindComparisonToQuotationPatternMatch)
