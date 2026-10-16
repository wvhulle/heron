module

meta import Heron.Assert
meta import Heron.Check.NestedOptionToOptionTransformer

-- IO wrapping Option with polymorphic return type and multiple parameters
#assertCheck nestedOptionToOptionTransformer in
def tryLookup {α : Type} (table : List (String × α)) (key : String) : IO (Option α) := sorry
becomes `(def tryLookup {α : Type} (table : List (String × α)) (key : String) : OptionT IO α := sorry)

-- Outer monad with args (Except as outer wrapping Option) — outer needs parens
#assertCheck nestedOptionToOptionTransformer in
def validate (input : String) : Except String (Option Nat) := sorry
becomes `(def validate (input : String) : OptionT (Except String) Nat := sorry)

#assertCheck nestedOptionToOptionTransformer in
def forwards (f : Nat → IO (Option Nat)) : IO (Option Nat) := f 0
becomes `(command| def forwards (f : Nat → OptionT IO Nat) : OptionT IO Nat := f 0)
