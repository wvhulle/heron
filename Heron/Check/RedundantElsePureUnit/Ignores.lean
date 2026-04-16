module

meta import Heron.Assert
meta import Heron.Check.RedundantElsePureUnit

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
