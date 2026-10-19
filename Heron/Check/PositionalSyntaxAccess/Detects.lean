module

meta import Heron.Assert
meta import Heron.Check.PositionalSyntaxAccess

#assertCheck positionalSyntaxAccess in
def firstArg (stx : Lean.Syntax) : Lean.Syntax := stx.getArg 0

#assertCheck positionalSyntaxAccess in
def firstArgIndexed (stx : Lean.Syntax) : Lean.Syntax := stx[0]

#assertCheck positionalSyntaxAccess in
def allArgs (stx : Lean.Syntax) : Array Lean.Syntax := stx.getArgs

#assertCheck positionalSyntaxAccess in
def everything (stx : Lean.Syntax) : Array Lean.Syntax := Heron.subtreeNodes stx

#assertCheck positionalSyntaxAccess in
def anyChild (stx : Lean.Syntax) : Bool := stx.getArgs.any (·.isMissing)
