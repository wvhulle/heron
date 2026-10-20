module

meta import Heron.Assert
meta import Heron.Check.SingleUseBindToNestedAction

#assertIgnore singleUseBindToNestedAction in
def usedTwice : IO Nat := do
  let n ← pure 1
  pure (n + n)

#assertIgnore singleUseBindToNestedAction in
def usedLater : IO Nat := do
  let n ← pure 1
  IO.println "between"
  pure n

#assertIgnore singleUseBindToNestedAction in
def effectOrderWouldChange (first second : IO Nat) : IO Nat := do
  let a ← first
  pure ((← second) + a)

#assertIgnore singleUseBindToNestedAction in
def usedInsideLambda (xs : List Nat) : IO (List Nat) := do
  let n ← pure 1
  pure (xs.map fun x => x + n)

#assertIgnore singleUseBindToNestedAction in
def usedInsideBranch (b : Bool) : IO Nat := do
  let n ← pure 1
  if b then
    pure n
  else
    pure 0
