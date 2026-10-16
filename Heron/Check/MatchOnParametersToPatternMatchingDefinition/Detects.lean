module

meta import Heron.Assert
meta import Heron.Check.MatchOnParametersToPatternMatchingDefinition

inductive Weekday where
  | monday | tuesday | wednesday | thursday | friday | saturday | sunday

#assertCheck matchOnParametersToPatternMatchingDefinition in
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _ => false
becomes `(command| def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false)

#assertCheck matchOnParametersToPatternMatchingDefinition in
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)
becomes `(command| def length : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (length ys))

#assertCheck matchOnParametersToPatternMatchingDefinition in
def fromOption (default : α) (opt : Option α) : α :=
  match opt with
  | none => default
  | some x => x
becomes `(command| def fromOption (default : α) : Option α → α
  | none => default
  | some x => x)

#assertCheck matchOnParametersToPatternMatchingDefinition in
def drop (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | 0, ys => ys
  | _, [] => []
  | k + 1, _ :: ys => drop k ys
becomes `(command| def drop : Nat → List α → List α
  | 0, ys => ys
  | _, [] => []
  | k + 1, _ :: ys => drop k ys)
