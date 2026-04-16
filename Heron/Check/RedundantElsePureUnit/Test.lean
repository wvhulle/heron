module

meta import Heron.Assert
meta import Heron.Check.RedundantElsePureUnit

#assertCheck redundantElsePureUnit in
example : IO Unit := do
  if true then
    IO.println "hello"
  else
    pure ()
becomes `(command|
example : IO Unit := do
  if true then
    IO.println "hello")

#assertIgnore redundantElsePureUnit in
  example : IO Unit := do
    if true then
      IO.println "hello"
    else
      IO.println "world"

#assertIgnore redundantElsePureUnit in
  example : IO Unit := do
    if true then
      IO.println "hello"
