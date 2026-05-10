module

meta import Heron.Assert
meta import Heron.Check.SyntaxKindCheck

#assertCheck syntaxKindCheck in
example (s : Lean.Syntax) : Bool := (s).getKind == ``Lean.Parser.Term.app
