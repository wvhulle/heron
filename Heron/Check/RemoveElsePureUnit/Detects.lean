module

meta import Heron.Assert
meta import Heron.Check.RemoveElsePureUnit

#assertCheck removeElsePureUnit in
example : IO Unit := do
  if true then
    IO.println "hello"
  else
    pure ()
becomes `(command|
example : IO Unit := do
  if true then
    IO.println "hello")
