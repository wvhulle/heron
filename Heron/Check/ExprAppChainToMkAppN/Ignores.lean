module

meta import Heron.Assert
meta import Heron.Check.ExprAppChainToMkAppN

-- Ignore: single application (no chain)
#assertIgnore exprAppChainToMkAppN in
def h (a b : Lean.Expr) := Expr.app a b

-- Ignore: already using mkAppN
#assertIgnore exprAppChainToMkAppN in
def k (a : Lean.Expr) (b : Array Lean.Expr) := mkAppN a b
