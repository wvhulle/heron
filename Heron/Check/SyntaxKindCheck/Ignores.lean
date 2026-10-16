module

meta import Heron.Assert
meta import Heron.Check.SyntaxKindCheck

-- Plain numeric equality, no `getKind`/`isOfKind` involved.
#assertIgnore syntaxKindCheck in
example (a b : Nat) : Bool := a == b

private structure Token where
  getKind : Nat

#assertIgnore syntaxKindCheck in
def userGetKindField (t : Token) : Bool := t.getKind == 0
