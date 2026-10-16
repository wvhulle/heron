module

meta import Heron.Assert
meta import Heron.Check.RedundantLetWildcard

#assertIgnore redundantLetWildcard in
example : IO Unit := do
  let x ← IO.getLine
  IO.println x

#assertIgnore redundantLetWildcard in
example : IO Unit := do
  IO.println "hello"

#assertIgnore redundantLetWildcard in
def discardsNatResult : IO Unit := do
  let _ ← (pure 5 : IO Nat)
  pure ()
