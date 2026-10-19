module

meta import Heron.Assert
meta import DeveloperTools.SelfLint.SyntaxKindOrAtomInspection

#assertIgnore syntaxKindOrAtomInspection in
def isLambda : Lean.Syntax → Bool
  | `(fun $_ => $_) => true
  | _ => false

private inductive Token where
  | word (text : String)

private def Token.getKind : Token → String
  | .word _ => "word"

#assertIgnore syntaxKindOrAtomInspection in
example (t : Token) : Bool := t.getKind == "word"
