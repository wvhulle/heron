module

meta import Heron.Assert
meta import Heron.Check.IfNotToUnless

#assertCheck ifNotToUnless in
example : IO Unit := do
  if not true then
    IO.println "hello"
becomes `(command|
example : IO Unit := do
  unless true do
    IO.println "hello")

#assertCheck ifNotToUnless in
example : IO Unit := do
  if !true then
    IO.println "hello"
becomes `(command|
example : IO Unit := do
  unless true do
    IO.println "hello")
