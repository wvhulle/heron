module

public meta import Heron.Check
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure SyntaxKindComparisonToQuotationPatternMatch where
  fullStx : TSyntax `term

private structure KindQuery where
  node : Syntax
  query : Syntax
  syntaxMethod : Name

private meta def isGetKindAccess : Syntax → Bool
  | `(($_:term).getKind) => true
  | `($x:ident) => isDottedAccess `getKind x.getId
  | _ => false

private meta def isIsOfKindCall : Syntax → Bool
  | `(($_:term).isOfKind $_) => true
  | `($fn:ident $_) => isDottedAccess `isOfKind fn.getId
  | _ => false

private meta def kindQuery? (node : Syntax) : Option KindQuery :=
  match node with
  | `($lhs == $_) | `($lhs != $_) =>
    if isGetKindAccess lhs then some { node, query := lhs, syntaxMethod := ``Lean.Syntax.getKind }
    else none
  | _ =>
    if isIsOfKindCall node then some { node, query := node, syntaxMethod := ``Lean.Syntax.isOfKind }
    else none

private meta def detectKindChecksBeforePositionalAccess (cmd : Syntax) :
    CommandElabM (Array SyntaxKindComparisonToQuotationPatternMatch) := do
  let queries := (subtreeNodes cmd).filterMap kindQuery?
  if queries.isEmpty then return #[]
  unless ← usesPositionalSyntaxAccess cmd do return #[]
  queries.filterMapM fun q => do
    unless ← elaboratesToApplicationOf q.query q.syntaxMethod do return none
    return some { fullStx := ⟨q.node⟩ }

private meta instance : Check SyntaxKindComparisonToQuotationPatternMatch where
  name := `syntaxKindComparisonToQuotationPattern
  kinds := #[]
  severity := .information
  category := .style
  detect := detectKindChecksBeforePositionalAccess
  message := fun _ => m!"Use an antiquotation pattern instead of a `Syntax.getKind` check followed by positional child access"
  emphasize := fun m => m.fullStx
  reference := some
    { topic := "Syntax pattern matching"
      url := "https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html#matching-on-syntax" }
  explanation := fun _ =>
    m!"Comparing a node's kind by name (e.g. `stx.getKind == ``Term.doLet`) only tells you which \
       parser produced the node; it binds none of its children. This declaration then reads \
       children by position (`getArg`, `getArgs`, `stx[i]`), which silently breaks when upstream \
       Lean changes the parser's layout. A `` `(...) `` antiquotation pattern checks the kind and \
       binds the children by name in one step, and is checked at compile time."
  replacements := fun _ => return #[]

meta initialize Check.register (α := SyntaxKindComparisonToQuotationPatternMatch)
