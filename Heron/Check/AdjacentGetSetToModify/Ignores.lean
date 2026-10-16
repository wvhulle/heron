module

meta import Heron.Assert
meta import Heron.Check.AdjacentGetSetToModify

private structure MyState where
  count : Nat
  name : String

-- Ignore: variable used between get and set
#assertIgnore adjacentGetSetToModify in
def f : StateM MyState Unit := do
  let st ← get
  IO.println s!"{st.count}"
  set { st with count := 0 }

-- Ignore: no set call
#assertIgnore adjacentGetSetToModify in
def g : StateM MyState Nat := do
  let s ← get
  pure s.count

#assertIgnore adjacentGetSetToModify in
def setUsesLaterBinding (next : StateM MyState Nat) : StateM MyState Unit := do
  let s ← get
  let v ← next
  set { s with count := v }

#assertIgnore adjacentGetSetToModify in
def stateReadAfterSet : StateM MyState Nat := do
  let s ← get
  set { s with count := 1 }
  return s.count
