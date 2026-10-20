module

public meta import Heron.EquationRewrite
meta import Heron.Register

open Lean Heron

private meta def ListFoldrOfMapToFoldr := EquationRewriteMatch

private meta instance : Check ListFoldrOfMapToFoldr := rewriteByEquation {
  name := `listFoldrOfMapToFoldr
  description := "Suggests one `List.foldr` that applies the mapped function itself instead of folding a mapped list."
  equation := ``List.foldr_map
  message := m!"Fold the original list and apply the mapped function inside the fold"
  label := m!"foldr map"
  explanation :=
    m!"Folding over a mapped list is the same as folding over the original list with the map \
       applied to each element inside the fold (`List.foldr_map`), which allocates no \
       intermediate list."
  sources := #[.hlint "Fuse foldr/map"] }

register_check ListFoldrOfMapToFoldr
