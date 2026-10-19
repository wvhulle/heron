module

meta import Heron.Assert
meta import Heron.Refactor.BindToDo

#assertRefactor bindToDo in
def f := IO.getLine >>= fun s => IO.println s
becomes `(def f := do
  let s ← IO.getLine
  IO.println s)

#assertRefactor bindToDo in
def g := IO.getLine >>= fun s => IO.getLine >>= fun t => IO.println (s ++ t)
becomes `(def g := do
  let s ← IO.getLine
  let t ← IO.getLine
  IO.println (s ++ t))
