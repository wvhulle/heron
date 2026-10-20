module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def ListMapIdToList := EquationRewriteMatch

private meta instance : Check ListMapIdToList := rewriteByEquation {
  name := `listMapIdToList
  description := "Suggests the list itself instead of mapping `id` over it."
  equation := ``List.map_id
  message := m!"Mapping `id` over a list returns the list unchanged"
  label := m!"map id"
  explanation := m!"Mapping the identity function over a list gives back the same list (`List.map_id`)."
  tags := #[.unnecessary]
  sources := #[.hlint "map id ==> id"] }

register_check ListMapIdToList
