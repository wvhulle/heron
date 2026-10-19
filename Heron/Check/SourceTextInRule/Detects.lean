module

meta import Heron.Assert
meta import Heron.Check.SourceTextInRule

#assertCheck sourceTextInRule in
def sourceOf (stx : Lean.Syntax) : Option String := stx.reprint

#assertCheck sourceTextInRule in
def isPrivateName (n : Lean.Name) : Bool := n.toString.startsWith "_private"

#assertCheck sourceTextInRule in
def words (s : String) : List String := s.splitOn " "
