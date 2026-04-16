module

meta import Heron.Assert
meta import Heron.Check.NestedMonadToJoin

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
