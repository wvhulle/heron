module

meta import Heron.Assert
meta import Heron.Check.SyntaxKindCheck

-- Plain numeric equality, no `getKind`/`isOfKind` involved.
#assertIgnore syntaxKindCheck in
example (a b : Nat) : Bool := a == b
