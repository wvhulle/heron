module

meta import Heron.Assert
meta import Heron.Check.NestedMonadToTransformer

#assertIgnore nestedMonadToTransformer in
  def h : Option Nat :=
    sorry

#assertIgnore nestedMonadToTransformer in
  def l : Option (Option Nat) :=
    sorry

#assertIgnore nestedMonadToTransformer in
def nestedTypeInBody : Nat := (fun (_ : IO (Option Nat)) => 0) (pure none)

#assertIgnore nestedMonadToTransformer in
  def k : Except String Nat :=
    sorry

#assertIgnore nestedMonadToTransformer in
def returnsNoneInBody : IO (Option Nat) := do
  return none

#assertIgnore nestedMonadToTransformer in
def returnsErrorInBody : IO (Except String Nat) := do
  return .error "failed"
