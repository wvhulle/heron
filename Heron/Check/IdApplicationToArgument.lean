module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def IdApplicationToArgument := EquationRewriteMatch

private meta instance : Check IdApplicationToArgument := rewriteByEquation {
  name := `idApplicationToArgument
  description := "Suggests the argument itself instead of applying `id` to it."
  equation := ``id_eq
  message := m!"Applying `id` returns the argument unchanged"
  label := m!"redundant id"
  explanation := m!"`id a` is `a` (`id_eq`)."
  tags := #[.unnecessary]
  sources := #[.hlint "Redundant id"] }

register_check IdApplicationToArgument
