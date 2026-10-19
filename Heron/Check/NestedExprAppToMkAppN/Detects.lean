module

meta import Heron.Assert
meta import Heron.Check.NestedExprAppToMkAppN

#assertCheck nestedExprAppToMkAppN in
  open Lean in
  def f (a b : Expr) :=
    Expr.app (Expr.app a a) b becomes
  `(open Lean in
  def f (a b : Expr) :=
    mkAppN a #[a, b])

#assertCheck nestedExprAppToMkAppN in
  def g (a b : Lean.Expr) : Lean.Expr :=
    .app (.app a a) b becomes
  `(def g (a b : Lean.Expr) : Lean.Expr :=
    mkAppN a #[a, b])

#assertCheck nestedExprAppToMkAppN in
  def h (a b c : Lean.Expr) :=
    Lean.Expr.app (Lean.Expr.app (Lean.Expr.app a a) b) c becomes
  `(def h (a b c : Lean.Expr) :=
    mkAppN a #[a, b, c])
