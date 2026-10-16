module

meta import Heron.Assert
meta import Heron.Check.NegatedIfToUnless

-- Ignore: has else branch
#assertIgnore negatedIfToUnless in
  example : IO Unit := do
    if not true then
      IO.println "hello"
    else
      IO.println "world"

-- Ignore: no negation
#assertIgnore negatedIfToUnless in
  example : IO Unit := do
    if true then
      IO.println "hello"
