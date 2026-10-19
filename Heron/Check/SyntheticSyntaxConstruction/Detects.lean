module

meta import Heron.Assert
meta import Heron.Check.SyntheticSyntaxConstruction

#assertCheck syntheticSyntaxConstruction in
def funKeyword : Lean.Syntax := Lean.mkAtom "fun"

#assertCheck syntheticSyntaxConstruction in
def transformerName : Lean.Ident := Lean.mkIdent `OptionT

#assertCheck syntheticSyntaxConstruction in
def one : Lean.NumLit := Lean.Syntax.mkNumLit (toString 1)

#assertCheck syntheticSyntaxConstruction in
def isNode : Lean.Syntax → Bool
  | .node _ _ _ => true
  | _ => false
