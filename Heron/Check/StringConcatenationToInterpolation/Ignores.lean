module

meta import Heron.Assert
meta import Heron.Check.StringConcatenationToInterpolation

#assertIgnore stringConcatenationToInterpolation in
def joinedLiterals : String := "abc" ++ "def"

#assertIgnore stringConcatenationToInterpolation in
def joinedLists (xs ys : List Nat) : List Nat := xs ++ ys

#assertIgnore stringConcatenationToInterpolation in
def joinedVariables (a b : String) : String := a ++ b

#assertIgnore stringConcatenationToInterpolation in
def alreadyInterpolated (n : Nat) : String := s!"n is {n}"
