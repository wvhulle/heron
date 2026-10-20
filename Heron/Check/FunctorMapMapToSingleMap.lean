module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def FunctorMapMapToSingleMap := EquationRewriteMatch

private meta instance : Check FunctorMapMapToSingleMap := rewriteByEquation {
  name := `functorMapMapToSingleMap
  description := "Suggests one `<$>` with a combined function instead of two consecutive maps over a lawful functor."
  equation := ``Functor.map_map
  message := m!"Map once with the combined function"
  label := m!"functor law"
  explanation :=
    m!"For a lawful functor, mapping `m` and then `g` is the same as mapping `fun a => g (m a)` \
       once (`Functor.map_map`)."
  sources := #[.hlint "Functor law"] }

register_check FunctorMapMapToSingleMap
