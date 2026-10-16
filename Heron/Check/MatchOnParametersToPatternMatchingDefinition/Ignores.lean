module

meta import Heron.Assert
meta import Heron.Check.MatchOnParametersToPatternMatchingDefinition

#assertIgnore matchOnParametersToPatternMatchingDefinition in
def parameterUsedInBody (n : Nat) : Nat :=
  match n with
  | 0 => n
  | k + 1 => k

#assertIgnore matchOnParametersToPatternMatchingDefinition in
def matchesOnlyTheFirst (n : Nat) (m : Nat) : Nat :=
  match n with
  | 0 => m
  | k + 1 => k

#assertIgnore matchOnParametersToPatternMatchingDefinition in
def withDefault (n : Nat := 0) : Nat :=
  match n with
  | 0 => 1
  | k + 1 => k

#assertIgnore matchOnParametersToPatternMatchingDefinition in
def dependentReturnType (n : Nat) : Fin (n + 1) :=
  match n with
  | 0 => 0
  | k + 1 => ⟨k, by omega⟩

#assertIgnore matchOnParametersToPatternMatchingDefinition in
def alreadyPatternMatching : Nat → Nat
  | 0 => 1
  | k + 1 => k
