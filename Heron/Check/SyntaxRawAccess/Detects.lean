module

meta import Heron.Assert
meta import Heron.Check.SyntaxRawAccess

#assertCheck syntaxRawAccess in
example (x : Lean.TSyntax `term) : Lean.Syntax := (x).raw
