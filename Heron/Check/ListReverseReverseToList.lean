module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def ListReverseReverseToList := EquationRewriteMatch

private meta instance : Check ListReverseReverseToList := rewriteByEquation {
  name := `listReverseReverseToList
  description := "Suggests the list itself instead of reversing it twice."
  equation := ``List.reverse_reverse
  message := m!"Reversing a list twice returns the list unchanged"
  label := m!"reverse reverse"
  explanation :=
    m!"Reversing a list twice gives back the same list (`List.reverse_reverse`), without \
       traversing it twice."
  tags := #[.unnecessary]
  sources := #[.hlint "Redundant reverse"] }

register_check ListReverseReverseToList
