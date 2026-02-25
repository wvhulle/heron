import Heron.Assert

namespace Heron.Assert

open Lean Elab Command

syntax (name := assertIgnoreCmd)
  "#assertIgnore " ident " in " command : command

@[command_elab assertIgnoreCmd] def elabAssertIgnore : CommandElab
  | stx@`(command| #assertIgnore $linterName in $cmd) => do
    let edits ← collectReplacements cmd linterName.getId
    unless edits.isEmpty do
      let text ← getFileMap
      let descriptions := edits.map fun edit =>
        let { before, after } := lspEditToSuggestionEdit text edit
        s!"  `{before.trimAscii}` => `{after.trimAscii}`"
      logWarningAt stx
        m!"expected no replacements but got {edits.size}:\n{"\n".intercalate descriptions.toList}"
  | _ => throwUnsupportedSyntax

end Heron.Assert
