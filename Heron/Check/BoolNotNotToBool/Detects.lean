module

meta import Heron.Assert
meta import Heron.Check.BoolNotNotToBool

#assertCheck boolNotNotToBool in
example (b : Bool) : Bool := !!b
becomes `(command|
example (b : Bool) : Bool := b)

#assertCheck boolNotNotToBool in
example (b : Bool) : Bool := not (not b)
becomes `(command|
example (b : Bool) : Bool := b)

#assertCheck boolNotNotToBool in
example (p q : Bool) : Bool := !!(p && q)
becomes `(command|
example (p q : Bool) : Bool := p && q)
