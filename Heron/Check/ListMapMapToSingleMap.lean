module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def ListMapMapToSingleMap := EquationRewriteMatch

private meta instance : Check ListMapMapToSingleMap := rewriteByEquation {
  name := `listMapMapToSingleMap
  description := "Suggests one `List.map` with a composed function instead of two consecutive maps."
  equation := ``List.map_map
  message := m!"Use one `List.map` with a composed function"
  label := m!"map fusion"
  explanation :=
    m!"Mapping `f` over a list and then mapping `g` over the result is the same as mapping \
       `g ∘ f` once (`List.map_map`), which traverses the list once and allocates no \
       intermediate list."
  sources := #[.hlint "Use map once"] }

register_check ListMapMapToSingleMap
