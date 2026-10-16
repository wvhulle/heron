module

meta import Heron.Assert
meta import Heron.Check.SyntaxKindComparisonToQuotationPattern

#assertCheck syntaxKindComparisonToQuotationPattern in
def firstArg (stx : Lean.Syntax) : Lean.Syntax :=
  if stx.getKind == ``Lean.Parser.Term.app then stx.getArg 0 else stx

#assertCheck syntaxKindComparisonToQuotationPattern in
def firstArgParenthesized (stx : Lean.Syntax) : Lean.Syntax :=
  if (stx).getKind != ``Lean.Parser.Term.app then stx else stx.getArg 0

#assertCheck syntaxKindComparisonToQuotationPattern in
def firstArgIndexed (stx : Lean.Syntax) : Lean.Syntax :=
  if stx.isOfKind ``Lean.Parser.Term.app then stx[0] else stx

#assertCheck syntaxKindComparisonToQuotationPattern in
def argCount (stx : Lean.Syntax) : Nat :=
  if (stx).isOfKind ``Lean.Parser.Term.app then stx.getArgs.size else 0
