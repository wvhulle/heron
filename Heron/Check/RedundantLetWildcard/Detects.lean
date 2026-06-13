module

meta import Heron.Assert
meta import Heron.Check.RedundantLetWildcard

#assertCheck redundantLetWildcard in
example : IO Unit := do
  let _ ← IO.println "hello"
  pure ()
becomes `(command|
example : IO Unit := do
  IO.println "hello"
  pure ())

-- A trailing comment must survive exactly once (not be duplicated by the rhs's trailing trivia).
#assertCheck redundantLetWildcard in
example : IO Unit := do
  let _ ← IO.println "hello" -- keep me
  pure ()
becomes `(command|
example : IO Unit := do
  IO.println "hello" -- keep me
  pure ())
