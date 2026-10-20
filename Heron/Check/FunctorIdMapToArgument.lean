module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def FunctorIdMapToArgument := EquationRewriteMatch

private meta instance : Check FunctorIdMapToArgument := rewriteByEquation {
  name := `functorIdMapToArgument
  description := "Suggests the value itself instead of mapping `id` over it."
  equation := ``id_map
  message := m!"Mapping `id` returns the value unchanged"
  label := m!"functor law"
  explanation := m!"For a lawful functor, `id <$> x` is `x` (`id_map`)."
  tags := #[.unnecessary]
  sources := #[.hlint "Functor law"] }

register_check FunctorIdMapToArgument
