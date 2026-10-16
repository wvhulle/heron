module

meta import Heron.Assert
meta import Heron.Check.SyntaxRawAccess

-- Field named `raw` on a user struct, not a TSyntax escape hatch.
private structure Box where
  raw : Nat

#assertIgnore syntaxRawAccess in
example (b : Box) : Nat := b.raw + 1

#assertIgnore syntaxRawAccess in
def parenthesizedBoxField (b : Box) : Nat := (b).raw + 1
