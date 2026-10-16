module

meta import Heron.Assert
meta import Heron.Check.SyntaxKindComparisonToQuotationPattern

-- Plain numeric equality, no `getKind`/`isOfKind` involved.
#assertIgnore syntaxKindComparisonToQuotationPattern in
example (a b : Nat) : Bool := a == b

private structure Token where
  getKind : Nat

#assertIgnore syntaxKindComparisonToQuotationPattern in
def userGetKindField (t : Token) : Bool := t.getKind == 0
