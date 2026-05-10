module

meta import Heron.Assert
meta import Heron.Check.ExceptToExceptT

-- IO wrapping Except with compound error type
#assertCheck exceptToExceptT in
def parseConfig (path : String) (strict : Bool) : IO (Except (List String) Nat) := sorry
becomes `(def parseConfig (path : String) (strict : Bool) : ExceptT (List String) IO Nat := sorry)
