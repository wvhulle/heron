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
