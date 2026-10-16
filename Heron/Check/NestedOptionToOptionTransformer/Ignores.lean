module

meta import Heron.Assert
meta import Heron.Check.NestedOptionToOptionTransformer

-- No outer monad wrapping — plain Option
#assertIgnore nestedOptionToOptionTransformer in
  def h : Option Nat :=
    sorry

-- Same-constructor nesting belongs to NestedMonadJoin, not this check
#assertIgnore nestedOptionToOptionTransformer in
  def l : Option (Option Nat) :=
    sorry

#assertIgnore nestedOptionToOptionTransformer in
def nestedTypeInBody : Nat := (fun (_ : IO (Option Nat)) => 0) (pure none)
