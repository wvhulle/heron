module

meta import Heron.Assert
meta import Heron.Check.SourcePositionInRule

#assertIgnore sourcePositionInRule in
def firstOfPair : Lean.Syntax → Option Lean.Syntax
  | `(($a, $_)) => some a
  | _ => none

private structure Cursor where
  offset : Nat

private def Cursor.getPos? (c : Cursor) : Option Nat := some c.offset

#assertIgnore sourcePositionInRule in
example (c : Cursor) : Option Nat := c.getPos?
