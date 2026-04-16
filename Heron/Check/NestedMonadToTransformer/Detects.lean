module

meta import Heron.Assert
meta import Heron.Check.NestedMonadToTransformer

-- IO wrapping Option with polymorphic return type and multiple parameters
#assertCheck nestedMonadToTransformer in
def tryLookup {α : Type} (table : List (String × α)) (key : String) : IO (Option α) := sorry
becomes `(def tryLookup {α : Type} (table : List (String × α)) (key : String) : OptionT IO α := sorry)

-- IO wrapping Except with compound error type
#assertCheck nestedMonadToTransformer in
def parseConfig (path : String) (strict : Bool) : IO (Except (List String) Nat) := sorry
becomes `(def parseConfig (path : String) (strict : Bool) : ExceptT (List String) IO Nat := sorry)

-- Outer monad with args (Except as outer wrapping Option) — outer needs parens
#assertCheck nestedMonadToTransformer in
def validate (input : String) : Except String (Option Nat) := sorry
becomes `(def validate (input : String) : OptionT (Except String) Nat := sorry)
