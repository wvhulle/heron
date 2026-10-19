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

#assertCheck removeElsePureUnit in
example (b : Bool) : IO Unit := do
  if b then
    IO.println "hello"
  else
    pure ()
  IO.println "after"
becomes `(command|
example (b : Bool) : IO Unit := do
  if b then
    IO.println "hello"
  IO.println "after")
