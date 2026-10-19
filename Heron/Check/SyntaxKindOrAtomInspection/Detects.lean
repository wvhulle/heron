module

meta import Heron.Assert
meta import Heron.Check.SyntaxKindOrAtomInspection

#assertCheck syntaxKindOrAtomInspection in
def isApp (stx : Lean.Syntax) : Bool := stx.getKind == `Lean.Parser.Term.app

#assertCheck syntaxKindOrAtomInspection in
def isAppToo (stx : Lean.Syntax) : Bool := stx.isOfKind `Lean.Parser.Term.app

#assertCheck syntaxKindOrAtomInspection in
def isLambdaSymbol (stx : Lean.Syntax) : Bool := stx.getAtomVal == "λ"
