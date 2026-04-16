module

meta import Heron.Assert
meta import Heron.Refactor.InlineAll

def myVal :=
  10

#assertIgnore inlineAllConst in
  example : Nat :=
    myVal

#assertIgnore inlineAllConst in
  def unused :=
    42

#assertIgnore inlineAllConst in
  def recFn : Nat → Nat
    | 0 => 0
    | n + 1 => recFn n

-- A recursive definition must not be inlined at its usage sites either — even
-- when Lean compiles the body via `brecOn`/`rec` and no self-reference
-- literally appears in the value.
def recFn2 : Nat → Nat
  | 0 => 0
  | n + 1 => recFn2 n

#assertIgnore inlineAllConst in
example : Nat := recFn2 1 + recFn2 2
