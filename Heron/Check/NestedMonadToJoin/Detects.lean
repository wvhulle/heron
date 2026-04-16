module

meta import Heron.Assert
meta import Heron.Check.NestedMonadToJoin

-- Nested Option in a function with multiple parameters
#assertCheck nestedMonadToJoin in
def flatten (xs : List Nat) (default : Nat) : Option (Option Nat) := sorry
becomes `(def flatten (xs : List Nat) (default : Nat) : Option Nat := sorry)

-- Nested Except with compound error type, buried in a signature with binders
#assertCheck nestedMonadToJoin in
def tryParse {α : Type} (input : String) : Except (List String) (Except (List String) α) := sorry
becomes `(def tryParse {α : Type} (input : String) : Except (List String) α := sorry)

-- Nested Option appearing in a let body type annotation
#assertCheck nestedMonadToJoin in
def g := let x : Option (Option (List Nat)) := none; x
becomes `(def g := let x : Option (List Nat) := none; x)
