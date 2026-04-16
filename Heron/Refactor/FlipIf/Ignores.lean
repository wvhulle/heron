module

meta import Heron.Assert
meta import Heron.Refactor.FlipIf

#assertIgnore flipIf in
def noFlip (p : Bool) (a b : Nat) : Nat := if p then a else b

-- `Bool.not p` is not `!p` in the syntax tree — only the `!` notation form is
-- offered for flipping.
#assertIgnore flipIf in
def notPrefix (p : Bool) (a b : Nat) : Nat := if Bool.not p then a else b

-- `if-then-else` without an `else` branch does not apply.
#assertIgnore flipIf in
def noElse : IO Unit := do if !true then IO.println "hi"
