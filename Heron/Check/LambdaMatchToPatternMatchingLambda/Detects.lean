module

meta import Heron.Assert
meta import Heron.Check.LambdaMatchToPatternMatchingLambda

#assertCheck lambdaMatchToPatternMatchingLambda in
  def f := fun x =>
    match x with
    | 0 => "zero"
    | _ => "other" becomes
  `(def f := fun
             | 0 => "zero"
             | _ => "other")
