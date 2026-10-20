module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def ListAllOfMapToComposedAll := EquationRewriteMatch

private meta instance : Check ListAllOfMapToComposedAll := rewriteByEquation {
  name := `listAllOfMapToComposedAll
  description := "Suggests `all` with a composed predicate instead of `all` over a mapped list."
  equation := ``List.all_map
  message := m!"Use `all` with a composed predicate instead of mapping first"
  label := m!"all map"
  explanation :=
    m!"Testing a predicate on every element of a mapped list is the same as testing the \
       composed predicate on the original list (`List.all_map`), which allocates no \
       intermediate list."
  sources := #[.hlint "all f (map g x) ==> all (f . g) x"] }

register_check ListAllOfMapToComposedAll
