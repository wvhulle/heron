module

meta import Heron.Assert
meta import Heron.Refactor.BindToDo

#assertIgnore bindToDo in
def h := [1, 2, 3].bind (fun x => [x, x])
