module

/-
Minimal, test-only leaf module referenced by `GenericExtra.lean`.
Nothing else in the project imports this, so it is only reachable via
`ExtraModUseUmbrella.lean` — which lets the unused-import analysis
observe a uniquely-covering umbrella in the generic test.
-/

public section

namespace DeadHeron.UnusedImport.ExtraModUseLeaf

def marker : Nat := 42

end DeadHeron.UnusedImport.ExtraModUseLeaf
