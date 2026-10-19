module

meta import Heron.Assert
meta import Heron.Check.NegatedIfToUnless

#assertCheck negatedIfToUnless in
example : IO Unit := do
  if not true then
    IO.println "hello"
becomes `(command|
example : IO Unit := do
  unless true do
    IO.println "hello")

#assertCheck negatedIfToUnless in
example : IO Unit := do
  if !true then
    IO.println "hello"
becomes `(command|
example : IO Unit := do
  unless true do
    IO.println "hello")

#assertCheck negatedIfToUnless in
example (line : String) : IO Unit := do
  if !(line.length >= 2) then
    -- keep this comment
    IO.println  "short"
becomes `(command|
example (line : String) : IO Unit := do
  unless (line.length >= 2) do
    -- keep this comment
    IO.println  "short")
