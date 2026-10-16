module

meta import Heron.Assert
meta import Heron.Check.RemoveLetWildcardOnUnitAction

#assertIgnore removeLetWildcardOnUnitAction in
example : IO Unit := do
  let x ← IO.getLine
  IO.println x

#assertIgnore removeLetWildcardOnUnitAction in
example : IO Unit := do
  IO.println "hello"

#assertIgnore removeLetWildcardOnUnitAction in
def discardsNatResult : IO Unit := do
  let _ ← (pure 5 : IO Nat)
  pure ()
