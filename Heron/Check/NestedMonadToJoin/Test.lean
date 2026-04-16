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

#assertIgnore nestedMonadToJoin in
  def h : Option Nat :=
    sorry

-- Different error types — not joinable
#assertIgnore nestedMonadToJoin in
  def k : Except String (Except Int Nat) :=
    sorry

-- Different constructors — not same-monad nesting
#assertIgnore nestedMonadToJoin in
  def l : Option (Except String Nat) :=
    sorry

-- Except with matching simple error but the arg types are complex
#assertIgnore nestedMonadToJoin in
  def m' : Except (List String) (Except (List Int) Nat) :=
    sorry
