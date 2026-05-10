module

meta import Heron.Assert
meta import Heron.Check.OptionToOptionT

-- IO wrapping Option with polymorphic return type and multiple parameters
#assertCheck optionToOptionT in
def tryLookup {α : Type} (table : List (String × α)) (key : String) : IO (Option α) := sorry
becomes `(def tryLookup {α : Type} (table : List (String × α)) (key : String) : OptionT IO α := sorry)

-- Outer monad with args (Except as outer wrapping Option) — outer needs parens
#assertCheck optionToOptionT in
def validate (input : String) : Except String (Option Nat) := sorry
becomes `(def validate (input : String) : OptionT (Except String) Nat := sorry)
