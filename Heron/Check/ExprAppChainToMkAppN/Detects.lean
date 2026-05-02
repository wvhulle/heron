module

meta import Heron.Assert
meta import Heron.Check.ExprAppChainToMkAppN

#assertCheck exprAppChainToMkAppN in
  def f (a b : Lean.Expr) :=
    Expr.app (Expr.app a a) b becomes
  `(def f (a b : Lean.Expr) :=
      mkAppN a #[a, b])

#assertCheck exprAppChainToMkAppN in
  def g (a b : Lean.Expr) :=
    .app (.app a a) b becomes
  `(def g (a b : Lean.Expr) :=
      mkAppN a #[a, b])

#assertCheck exprAppChainToMkAppN in
  def h (a b c : Lean.Expr) :=
    Expr.app (Expr.app (Expr.app a a) b) c becomes
  `(def h (a b c : Lean.Expr) :=
      mkAppN a #[a, b, c])
