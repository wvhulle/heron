module

meta import Heron.Assert
meta import Heron.Refactor.Inline

-- The definition site of `d` should not flag `d` itself for inlining.
#assertIgnore inline in
  def d :=
    0
