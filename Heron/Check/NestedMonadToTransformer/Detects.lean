module

meta import Heron.Assert
meta import Heron.Check.NestedMonadToTransformer

#assertCheck nestedMonadToTransformer in
def tryLookup {α : Type} (table : List (String × α)) (key : String) : IO (Option α) := sorry

#assertCheck nestedMonadToTransformer in
def validate (input : String) : Except String (Option Nat) := sorry

#assertCheck nestedMonadToTransformer in
def forwards (f : Nat → IO (Option Nat)) : IO (Option Nat) := f 0

#assertCheck nestedMonadToTransformer in
def parseConfig (path : String) (strict : Bool) : IO (Except (List String) Nat) := sorry
