module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def PureBindToApplication := EquationRewriteMatch

private meta instance : Check PureBindToApplication := rewriteByEquation {
  name := `pureBindToApplication
  description := "Suggests applying the continuation directly instead of binding a `pure` value."
  equation := ``pure_bind
  message := m!"Apply the function directly instead of binding `pure`"
  label := m!"monad law"
  explanation := m!"For a lawful monad, `pure x >>= f` is `f x` (`pure_bind`)."
  sources := #[.hlint "Monad law, left identity"] }

register_check PureBindToApplication
