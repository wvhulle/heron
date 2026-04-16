module

meta import Heron.Assert
meta import Heron.Check.GetSetToModify

private structure MyState where
  count : Nat
  name : String

-- Basic get/set to modify
#assertCheck getSetToModify in
def inc : StateM MyState Unit := do
  let s ← get
  set { s with count := s.count + 1 }
becomes `(command|
def inc : StateM MyState Unit := do
  modify fun s => { s with count := s.count + 1 })
