module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def ListFlattenOfMapToFlatMap := EquationRewriteMatch

private meta instance : Check ListFlattenOfMapToFlatMap := rewriteByEquation {
  name := `listFlattenOfMapToFlatMap
  description := "Suggests `List.flatMap` instead of flattening a mapped list."
  equation := ``List.flatMap_def
  rightToLeft := true
  message := m!"Use `List.flatMap` instead of flattening a mapped list"
  label := m!"flatten map"
  explanation :=
    m!"Flattening the result of a map is `List.flatMap` (`List.flatMap_def`), which builds the \
       result without the intermediate list of lists."
  sources := #[.hlint "Use concatMap"] }

register_check ListFlattenOfMapToFlatMap
