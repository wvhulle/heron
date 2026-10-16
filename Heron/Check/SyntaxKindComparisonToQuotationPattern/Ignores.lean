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

#assertIgnore syntaxKindComparisonToQuotationPattern in
def isDeclaration (stx : Lean.Syntax) : Bool := stx.isOfKind ``Lean.Parser.Command.declaration

#assertIgnore syntaxKindComparisonToQuotationPattern in
def isApplication (s : Lean.Syntax) : Bool := s.getKind == ``Lean.Parser.Term.app

#assertIgnore syntaxKindComparisonToQuotationPattern in
def isCheckCommand (c : Lean.TSyntax `command) : Bool := c.raw.getKind == ``Lean.Parser.Command.check
