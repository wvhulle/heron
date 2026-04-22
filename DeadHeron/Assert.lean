module

public meta import Heron.Assert
public meta import DeadHeron.ImportAnalysis

public section

namespace Heron.Assert

open Lean Elab Command Heron

/-- Collect all identifiers anywhere inside a syntax tree. -/
private meta partial def collectIdents (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId]
  else stx.getArgs.foldl (init := #[]) fun acc child => acc ++ collectIdents child

/-- Sort names using `Name.cmp` so `Array.==` comparisons are order-independent. -/
private meta def sortNames (xs : Array Name) : Array Name :=
  xs.qsort fun a b => Name.cmp a b == .lt

syntax (name := assertImportsCmd)
  "#assertImports"
    (ppSpace &"unused" " := " "[" ident,* "]")?
    (ppSpace &"overPublic" " := " "[" ident,* "]")?
    (ppSpace &"overMeta" " := " "[" ident,* "]")? : command

@[command_elab assertImportsCmd] meta def elabAssertImports : CommandElab := fun stx => do
  Lean.recordExtraModUse `DeadHeron.Assert (isMeta := true)
  let expectedUnused := sortNames (collectIdents stx[1])
  let expectedOverPublic := sortNames (collectIdents stx[2])
  let expectedOverMeta := sortNames (collectIdents stx[3])
  let analyses ← ImportAnalysis.analyzeImports stx
  if analyses.isEmpty then
    logErrorAt stx
      m!"no imports were analyzed — `#assertImports` must be the last command of the file"
    return
  let actualUnused := sortNames <| analyses.filterMap fun a =>
    if !a.isUsed then some a.imp.module else none
  let actualOverPublic := sortNames <| analyses.filterMap fun a =>
    if a.isUsed && a.imp.isExported && !a.needsExported then some a.imp.module else none
  let actualOverMeta := sortNames <| analyses.filterMap fun a =>
    if a.isUsed && a.imp.isMeta && !a.needsMeta then some a.imp.module else none
  if actualUnused != expectedUnused then
    logErrorAt stx
      m!"unused imports mismatch:\n  expected: {expectedUnused}\n  actual:   {actualUnused}"
  if actualOverPublic != expectedOverPublic then
    logErrorAt stx
      m!"over-public imports mismatch:\n  expected: {expectedOverPublic}\n  actual:   {actualOverPublic}"
  if actualOverMeta != expectedOverMeta then
    logErrorAt stx
      m!"over-meta imports mismatch:\n  expected: {expectedOverMeta}\n  actual:   {actualOverMeta}"

end Heron.Assert
