module

meta import Heron.Assert
meta import Heron.Refactor.BindToDo

#assertIgnore bindToDo in
def h := [1, 2, 3].bind (fun x => [x, x])

-- `>>=` whose right side is not a `fun` is not a rewritable bind-chain.
#assertIgnore bindToDo in
def i (xs : List Nat) (f : Nat → List Nat) := xs >>= f

-- `>>=` with a multi-parameter `fun` is not a simple `let ← … ;` binding.
#assertIgnore bindToDo in
def j (xs : List Nat) := xs >>= (fun x y => [x + y])
