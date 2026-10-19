module

meta import Heron.Assert
meta import Heron.Check.SyntheticSyntaxConstruction

#assertIgnore syntheticSyntaxConstruction in
def identity : Lean.MacroM Lean.Syntax := `(fun x => x)

#assertIgnore syntheticSyntaxConstruction in
def rebuild : Lean.Syntax → Lean.MacroM Lean.Syntax
  | `(($a, $b)) => `(($b, $a))
  | _ => Lean.Macro.throwUnsupported

#assertIgnore syntheticSyntaxConstruction in
def one : Lean.NumLit := Lean.quote (1 : Nat)

#assertIgnore syntheticSyntaxConstruction in
def spanOf (first last : Lean.Syntax) : Lean.Syntax := Lean.mkNullNode #[first, last]

#assertIgnore syntheticSyntaxConstruction in
def constructorsByName : Array Lean.Name := #[``Lean.mkAtom, ``Lean.Syntax.node]

#assertIgnore syntheticSyntaxConstruction in
def identifierOfResolvedName (resolved : Lean.Name) : Lean.Ident := Lean.mkIdent resolved
