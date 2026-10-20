module

meta import Heron.Assert
meta import Heron.Check.BoolNotNotToBool

#assertIgnore boolNotNotToBool in
example (b : Bool) : Bool := !b
