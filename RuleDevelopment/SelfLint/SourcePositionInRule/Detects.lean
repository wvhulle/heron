module

meta import Heron.Assert
meta import RuleDevelopment.SelfLint.SourcePositionInRule

#assertCheck sourcePositionInRule in
def startsBefore (a b : Lean.Syntax) : Bool := a.getPos? < b.getPos?

#assertCheck sourcePositionInRule in
def spanOf (stx : Lean.Syntax) : Option Lean.String.Range := stx.getRange?
