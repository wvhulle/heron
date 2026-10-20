module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def BindPureToArgument := EquationRewriteMatch

private meta instance : Check BindPureToArgument := rewriteByEquation {
  name := `bindPureToArgument
  description := "Suggests the action itself instead of binding it to `pure`."
  equation := ``bind_pure
  message := m!"Binding to `pure` returns the action unchanged"
  label := m!"monad law"
  explanation := m!"For a lawful monad, `x >>= pure` is `x` (`bind_pure`)."
  tags := #[.unnecessary]
  sources := #[.hlint "Monad law, right identity"] }

register_check BindPureToArgument
