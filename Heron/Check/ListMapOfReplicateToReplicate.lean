module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def ListMapOfReplicateToReplicate := EquationRewriteMatch

private meta instance : Check ListMapOfReplicateToReplicate := rewriteByEquation {
  name := `listMapOfReplicateToReplicate
  description := "Suggests replicating the mapped element instead of mapping over a replicated list."
  equation := ``List.map_replicate
  message := m!"Replicate the mapped element instead of mapping over copies"
  label := m!"map replicate"
  explanation :=
    m!"Mapping `f` over `n` copies of `a` gives `n` copies of `f a` (`List.map_replicate`), \
       which applies `f` once."
  sources := #[.hlint "map f (replicate n x) ==> replicate n (f x)"] }

register_check ListMapOfReplicateToReplicate
