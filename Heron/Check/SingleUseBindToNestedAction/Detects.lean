module

meta import Heron.Assert
meta import Heron.Check.SingleUseBindToNestedAction

#assertCheck singleUseBindToNestedAction in
def mapM' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM' f xs
    pure (hd :: tl)
becomes `(command| def mapM' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    pure (hd :: (← mapM' f xs)))

#assertCheck singleUseBindToNestedAction in
def mapM'' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    pure (hd :: (← mapM'' f xs))
becomes `(command| def mapM'' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure ((← f x) :: (← mapM'' f xs)))

#assertCheck singleUseBindToNestedAction in
def innerLambdaReusesTheName (next : IO Nat) : IO Nat := do
  let n ← next
  pure ((fun n => n) 2 + n)
becomes `(command| def innerLambdaReusesTheName (next : IO Nat) : IO Nat := do
  pure ((fun n => n) 2 + (← next)))

#assertCheck singleUseBindToNestedAction in
def usedAsMatchDiscriminant (read : IO (Option Nat)) : IO Nat := do
  let chunk? ← read
  -- the discriminant comes from the bind above
  match chunk? with
  | none => return 0  -- end of input
  | some chunk => return chunk
becomes `(command| def usedAsMatchDiscriminant (read : IO (Option Nat)) : IO Nat := do
  -- the discriminant comes from the bind above
  match (← read) with
  | none => return 0  -- end of input
  | some chunk => return chunk)

#assertCheck singleUseBindToNestedAction in
def usedInIfCondition (ready : IO Bool) : IO Nat := do
  let isReady ← ready
  if isReady then
    return 1
  return 0
becomes `(command| def usedInIfCondition (ready : IO Bool) : IO Nat := do
  if (← ready) then
    return 1
  return 0)
