module

meta import Heron.Assert
meta import Heron.Check.StringConcatenationToInterpolation

#assertCheck stringConcatenationToInterpolation in
def describe (n : Nat) : String := "three fives is " ++ toString (n * 3)

#assertCheck stringConcatenationToInterpolation in
def greeting (name : String) : String := "Hello, " ++ name ++ "!"

#assertCheck stringConcatenationToInterpolation in
def extended (n : Nat) : String := s!"n is {n}" ++ "."
