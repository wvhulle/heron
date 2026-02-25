import Heron.Assert

namespace Heron.Assert

open Lean Elab Command

syntax (name := assertFixCmd)
  "#assertFix " ident sepBy1(replacementPair, ", ") " in " command : command

@[command_elab assertFixCmd] def elabAssertFix : CommandElab
  | stx@`(command| #assertFix $linterName $pairs,* in $cmd) => do
    let edits ← collectReplacements cmd linterName.getId
    let text ← getFileMap
    let pairStxs := pairs.getElems
    if edits.size != pairStxs.size then
      logWarningAt stx m!"expected {pairStxs.size} replacement(s) but got {edits.size}"
      return
    let results ← (edits.zip pairStxs).mapIdxM fun idx (edit, pairStx) =>
      verifyReplacementPair text edit pairStx (idx + 1)
    unless results.all (·) do return
  | _ => throwUnsupportedSyntax

end Heron.Assert
