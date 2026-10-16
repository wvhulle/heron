module

meta import Heron.Assert
meta import Heron.Check.SyntaxKindComparisonToQuotationPattern

#assertCheck syntaxKindComparisonToQuotationPattern in
example (s : Lean.Syntax) : Bool := (s).getKind == ``Lean.Parser.Term.app

#assertCheck syntaxKindComparisonToQuotationPattern in
example (s : Lean.Syntax) : Bool := s.getKind == ``Lean.Parser.Term.app

#assertCheck syntaxKindComparisonToQuotationPattern in
example (s : Lean.Syntax) : Bool := s.getKind != ``Lean.Parser.Term.app

#assertCheck syntaxKindComparisonToQuotationPattern in
example (s : Lean.Syntax) : Bool := s.isOfKind ``Lean.Parser.Term.app
