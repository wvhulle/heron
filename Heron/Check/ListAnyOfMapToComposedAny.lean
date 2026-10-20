module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def ListAnyOfMapToComposedAny := EquationRewriteMatch

private meta instance : Check ListAnyOfMapToComposedAny := rewriteByEquation {
  name := `listAnyOfMapToComposedAny
  description := "Suggests `any` with a composed predicate instead of `any` over a mapped list."
  equation := ``List.any_map
  message := m!"Use `any` with a composed predicate instead of mapping first"
  label := m!"any map"
  explanation :=
    m!"Testing a predicate on a mapped list is the same as testing the composed predicate on \
       the original list (`List.any_map`), which allocates no intermediate list."
  sources := #[.hlint "any f (map g x) ==> any (f . g) x"] }

register_check ListAnyOfMapToComposedAny
