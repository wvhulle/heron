module

meta import Heron.Assert
meta import Heron.Check.ExprAppChainToMkAppN

#assertCheck exprAppChainToMkAppN in
def f (a b : Lean.Expr) := Expr.app (Expr.app a a) b
becomes `(def f (a b : Lean.Expr) := mkAppN a #[a, b])

#assertCheck exprAppChainToMkAppN in
def g (a b : Lean.Expr) := .app (.app a a) b
becomes `(def g (a b : Lean.Expr) := mkAppN a #[a, b])

-- Ignore: single application (no chain)
#assertIgnore exprAppChainToMkAppN in
def h (a b : Lean.Expr) := Expr.app a b

-- Ignore: already using mkAppN
#assertIgnore exprAppChainToMkAppN in
def k (a : Lean.Expr) (b : Array Lean.Expr) := mkAppN a b
