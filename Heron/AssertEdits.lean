import Heron.Assert

namespace Heron.Assert

open Lean Elab Command Meta Term.Quotation

syntax (name := assertEditsCmd)
  "#assertEdits " ident sepBy1(suggestionPair, ", ") " in " command : command

@[command_elab assertEditsCmd] def elabAssertEdits : CommandElab
  | stx@`(command| #assertEdits $linterName $pairs,* in $cmd) => do
    let edits ← elabCommandAndCollectSuggestionEdits cmd (some linterName.getId)
    let text ← getFileMap
    let pairStxs := pairs.getElems
    let catName ← if h : 0 < pairStxs.size then
        match pairStxs[0] with
        | `(suggestionPair| $before => $_) => liftTermElabM (getQuotKind before)
        | _ => pure `tactic
      else pure `tactic
    if edits.size != pairStxs.size then
      logWarningAt stx m!"expected {pairStxs.size} edit(s) but got {edits.size}"
      pushMismatchToInfoTree stx catName (some linterName.getId) (edits.map (lspEditToSuggestionEdit text))
      return
    let results ← (edits.zip pairStxs).mapIdxM fun idx (edit, pairStx) =>
      verifySuggestionPair text edit pairStx (idx + 1)
    unless results.all (·.2) do
      pushMismatchToInfoTree stx catName (some linterName.getId) (results.map (·.1))
  | _ => throwUnsupportedSyntax

end Heron.Assert
