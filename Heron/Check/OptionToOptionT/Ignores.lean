module

meta import Heron.Assert
meta import Heron.Check.OptionToOptionT

-- No outer monad wrapping — plain Option
#assertIgnore optionToOptionT in
  def h : Option Nat :=
    sorry

-- Same-constructor nesting belongs to NestedMonadJoin, not this check
#assertIgnore optionToOptionT in
  def l : Option (Option Nat) :=
    sorry
