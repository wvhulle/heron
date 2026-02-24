import Heron.Assert

namespace Heron.Assert

open Lean Elab Command

syntax (name := assertNoSuggestsCmd)
  "#assertNoSuggests " (ident)? "in " command : command

@[command_elab assertNoSuggestsCmd] def elabAssertNoSuggests : CommandElab
  | stx@`(command| #assertNoSuggests $[$linterName?:ident]? in $cmd) => do
    let edits ← elabCommandAndCollectSuggestionEdits cmd (linterName?.map (·.getId))
    unless edits.isEmpty do
      let text ← getFileMap
      let descriptions := edits.map fun edit =>
        let { before, after } := lspEditToSuggestionEdit text edit
        s!"  `{before.trimAscii}` => `{after.trimAscii}`"
      logWarningAt stx
        m!"expected no suggestions but got {edits.size}:\n{"\n".intercalate descriptions.toList}"
  | _ => throwUnsupportedSyntax

end Heron.Assert
