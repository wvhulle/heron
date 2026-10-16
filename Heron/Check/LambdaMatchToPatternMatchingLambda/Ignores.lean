module

meta import Heron.Assert
meta import Heron.Check.LambdaMatchToPatternMatchingLambda

-- Ignore: multiple parameters
#assertIgnore lambdaMatchToPatternMatchingLambda in
  def g := fun x y =>
    match x with
    | 0 => y
    | _ =>
      0

-- Ignore: match on different variable
#assertIgnore lambdaMatchToPatternMatchingLambda in
  def h (y : Nat) := fun x =>
    match y with
    | 0 => x
    | _ =>
      0

-- Ignore: already using fun | syntax
#assertIgnore lambdaMatchToPatternMatchingLambda in
  def k := fun
    | 0 => "zero"
    | _ => "other"

#assertIgnore lambdaMatchToPatternMatchingLambda in
def armUsesParameter := fun (x : Nat) => match x with
  | 0 => x
  | _ => 1
