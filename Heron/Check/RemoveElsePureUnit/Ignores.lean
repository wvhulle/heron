module

meta import Heron.Assert
meta import Heron.Check.RemoveElsePureUnit

#assertIgnore removeElsePureUnit in
  example : IO Unit := do
    if true then
      IO.println "hello"
    else
      IO.println "world"

#assertIgnore removeElsePureUnit in
  example : IO Unit := do
    if true then
      IO.println "hello"
