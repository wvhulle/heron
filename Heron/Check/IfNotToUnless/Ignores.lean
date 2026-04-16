module

meta import Heron.Assert
meta import Heron.Check.IfNotToUnless

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
