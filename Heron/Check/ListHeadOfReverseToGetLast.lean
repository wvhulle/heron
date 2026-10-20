module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def ListHeadOfReverseToGetLast := EquationRewriteMatch

private meta instance : Check ListHeadOfReverseToGetLast := rewriteByEquation {
  name := `listHeadOfReverseToGetLast
  description := "Suggests `getLast?` instead of the head of the reversed list."
  equation := ``List.head?_reverse
  message := m!"Use `getLast?` instead of the head of the reversed list"
  label := m!"head reverse"
  explanation :=
    m!"The first element of the reversed list is the last element of the list \
       (`List.head?_reverse`), which `getLast?` finds without building the reversed list."
  sources := #[.hlint "head (reverse x) ==> last x"] }

register_check ListHeadOfReverseToGetLast
