module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def BoolNotNotToBool := EquationRewriteMatch

private meta instance : Check BoolNotNotToBool := rewriteByEquation {
  name := `boolNotNotToBool
  description := "Suggests the Boolean itself instead of negating it twice."
  equation := ``Bool.not_not
  message := m!"Negating a Boolean twice returns it unchanged"
  label := m!"redundant not"
  explanation := m!"`!!b` is `b` (`Bool.not_not`)."
  tags := #[.unnecessary]
  sources := #[.hlint "Redundant not"] }

register_check BoolNotNotToBool
