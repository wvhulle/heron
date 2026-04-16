import Heron.Assert
import Heron.Check.IfNotToUnless

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

-- Ignore: has else branch
#assertIgnore ifNotToUnless in
  example : IO Unit := do
    if not true then
      IO.println "hello"
    else
      IO.println "world"

-- Ignore: no negation
#assertIgnore ifNotToUnless in
  example : IO Unit := do
    if true then
      IO.println "hello"
