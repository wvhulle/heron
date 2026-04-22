module

/-
Umbrella re-export of `ExtraModUseLeaf`. Used by `GenericExtra.lean`
to verify that the analysis keeps an umbrella import when it is the
unique cover for a module recorded via `Lean.recordExtraModUse`.
-/
public import DeadHeron.UnusedImport.ExtraModUseLeaf
