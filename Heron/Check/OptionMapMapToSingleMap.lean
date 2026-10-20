module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def OptionMapMapToSingleMap := EquationRewriteMatch

private meta instance : Check OptionMapMapToSingleMap := rewriteByEquation {
  name := `optionMapMapToSingleMap
  description := "Suggests one `Option.map` with a composed function instead of two consecutive maps."
  equation := ``Option.map_map
  message := m!"Use one `Option.map` with a composed function"
  label := m!"map fusion"
  explanation := m!"Mapping `g` and then `h` over an option is the same as mapping `h ∘ g` once (`Option.map_map`)."
  sources := #[.hlint "Functor law"] }

register_check OptionMapMapToSingleMap
