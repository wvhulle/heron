import Heron.Assert
import Heron.Check.RedundantLetWildcard

#assertCheck redundantLetWildcard in
example : IO Unit := do
  let _ ← IO.println "hello"
  pure ()
becomes `(command|
example : IO Unit := do
  IO.println "hello"
  pure ())

#assertIgnore redundantLetWildcard in
example : IO Unit := do
  let x ← IO.getLine
  IO.println x

#assertIgnore redundantLetWildcard in
example : IO Unit := do
  IO.println "hello"
