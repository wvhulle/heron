import Heron.Assert

namespace Heron.Assert

open Lean Elab Command Server Meta Term.Quotation

syntax (name := assertSuggestsCmd)
  "#assertSuggests " (ident)? sepBy1(suggestionPair, ", ") " in " command : command

@[command_elab assertSuggestsCmd] def elabAssertSuggests : CommandElab
  | stx@`(command| #assertSuggests $[$linterName?:ident]? $pairs,* in $cmd) => do
    let linterName? := linterName?.map (·.getId)
    let edits ← elabCommandAndCollectSuggestionEdits cmd linterName?
    let text ← getFileMap
    let pairStxs := pairs.getElems
    let catName ← if h : 0 < pairStxs.size then
        match pairStxs[0] with
        | `(suggestionPair| $before => $_) => liftTermElabM (getQuotKind before)
        | _ => pure `tactic
      else pure `tactic
    if edits.size != pairStxs.size then
      logWarningAt stx m!"expected {pairStxs.size} suggestion(s) but got {edits.size}"
      pushMismatchToInfoTree stx catName linterName? (edits.map (lspEditToSuggestionEdit text))
      return
    let results ← (edits.zip pairStxs).mapIdxM fun idx (edit, pairStx) =>
      verifySuggestionPair text edit pairStx (idx + 1)
    unless results.all (·.2) do
      pushMismatchToInfoTree stx catName linterName? (results.map (·.1))
  | _ => throwUnsupportedSyntax

open CodeAction Server RequestM in
@[command_code_action assertSuggestsCmd]
def updateAssertSuggestsCodeAction : CommandCodeAction := fun _ _ _ node => do
  let .node _ ts := node | return #[]
  let mismatch? := ts.findSome? fun
    | .node (.ofCustomInfo { stx, value }) _ => do
      let m ← value.get? SuggestionMismatch; return (stx, m)
    | _ => none
  let some (stx, mismatch) := mismatch? | return #[]
  let doc ← readDoc
  let baseCodeAction := {
    title := "Update #assertSuggests with actual suggestions"
    kind? := "quickfix"
    isPreferred? := true
  }
  pure #[{
    eager := baseCodeAction
    lazy? := some do
      let some start := stx.getPos? true | return baseCodeAction
      let some inKeywordPos := stx[3].getPos? true | return baseCodeAction
      let newText := renderAssertSuggestsPrefix mismatch.catName mismatch.linterName? mismatch.actualEdits
      pure { baseCodeAction with
        edit? := some <| .ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, inKeywordPos⟩
          newText
        }
      }
  }]

end Heron.Assert
