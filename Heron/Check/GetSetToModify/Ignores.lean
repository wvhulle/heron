module

meta import Heron.Assert
meta import Heron.Check.GetSetToModify

private structure MyState where
  count : Nat
  name : String

-- Ignore: variable used between get and set
#assertIgnore getSetToModify in
def f : StateM MyState Unit := do
  let st ← get
  IO.println s!"{st.count}"
  set { st with count := 0 }

-- Ignore: no set call
#assertIgnore getSetToModify in
def g : StateM MyState Nat := do
  let s ← get
  pure s.count
