import Lean.Elab.Command
import Lean.Elab.Quotation
import Heron.Rule

namespace Heron.Assert

open Lean Elab Command Heron

private def elabCommandSilently (cmd : Syntax) : CommandElabM Unit :=
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    withReader ({ · with snap? := none }) do
      try elabCommand cmd catch _ => pure ()

/-- Collect all `TextEdit`s produced by a rule for a command.

Looks up the rule's runner by name and calls it directly — the same
`Rule.detect` + `Rule.replacements` + `Replacement.toTextEdit?` path
used by the code action providers. -/
def collectReplacements (cmd : Syntax) (linterName : Name)
    : CommandElabM (Array Lsp.TextEdit) := do
  let runners ← ruleRunnersRef.get
  let some runner := runners[linterName]? | do
    throwError "no rule runner registered for '{linterName}'"
  -- Elaborate the command so that rules needing info trees can find them.
  -- Save and restore messages to suppress any diagnostics from elaboration.
  withScope (fun scope => { scope with opts := scope.opts.insert (`linter ++ linterName) (.ofBool true) }) do
    let savedMessages := (← get).messages
    withoutModifyingEnv do
      elabCommandSilently cmd
      let edits ← runner cmd
      modify fun s => { s with messages := savedMessages }
      return edits

/-- Apply an array of non-overlapping LSP `TextEdit`s to a source string.

Edits are sorted by range start descending and applied back-to-front so that
earlier byte offsets remain valid, matching the LSP specification that all
ranges refer to the original document. -/
def applyEdits (text : FileMap) (edits : Array Lsp.TextEdit) : String :=
  let sorted := edits.qsort fun a b =>
    let aStart := text.lspPosToUtf8Pos a.range.start
    let bStart := text.lspPosToUtf8Pos b.range.start
    bStart < aStart
  sorted.foldl (init := text.source) fun src edit =>
    let startPos := text.lspPosToUtf8Pos edit.range.start
    let endPos := text.lspPosToUtf8Pos edit.range.end
    let pre := String.Pos.Raw.extract src 0 startPos
    let post := String.Pos.Raw.extract src endPos src.rawEndPos
    pre ++ edit.newText ++ post

/-- Verify that applying all edits from a rule to `cmd` produces the text in
the `expected` quotation. -/
private def elabAssertResult (linterName : Ident) (cmd : Syntax)
    (expectedQuot : Syntax) (stx : Syntax) : CommandElabM Unit := do
  let edits ← collectReplacements cmd linterName.getId
  if edits.isEmpty then
    logWarningAt stx m!"expected replacements but got none"
    return
  let text ← getFileMap
  let some cmdRange := cmd.getRange? | do
    logWarningAt stx m!"command has no source range"
    return
  let original := String.Pos.Raw.extract text.source cmdRange.start cmdRange.stop
  let modified := applyEdits text edits
  let delta : Int := modified.rawEndPos.byteIdx - text.source.rawEndPos.byteIdx
  let newStop : Nat := (cmdRange.stop.byteIdx : Int) + delta |>.toNat
  let actual := String.Pos.Raw.extract modified cmdRange.start ⟨newStop⟩
  let some expectedText := expectedQuot.getQuotContent.reprint | do
    logWarningAt stx m!"could not reprint expected quotation"
    return
  let actualTrimmed := actual.trimAscii
  let expectedTrimmed := expectedText.trimAscii
  unless actualTrimmed == expectedTrimmed do
    logErrorAt stx
      m!"result mismatch:\n  expected: \"{expectedTrimmed}\"\n  actual:   \"{actualTrimmed}\"\n  original: \"{original.trimAscii}\""

syntax (name := assertCheckCmd)
  "#assertCheck " ident " in " command " becomes " term : command

syntax (name := assertRefactorCmd)
  "#assertRefactor " ident " in " command " becomes " term : command

@[command_elab assertCheckCmd] def elabAssertCheck : CommandElab
  | stx@`(command| #assertCheck $linterName in $cmd becomes $expected) =>
    elabAssertResult linterName cmd expected stx
  | _ => throwUnsupportedSyntax

@[command_elab assertRefactorCmd] def elabAssertRefactor : CommandElab
  | stx@`(command| #assertRefactor $linterName in $cmd becomes $expected) =>
    elabAssertResult linterName cmd expected stx
  | _ => throwUnsupportedSyntax

syntax (name := assertIgnoreCmd)
  "#assertIgnore " ident " in " command : command

@[command_elab assertIgnoreCmd] def elabAssertIgnore : CommandElab
  | stx@`(command| #assertIgnore $linterName in $cmd) => do
    let edits ← collectReplacements cmd linterName.getId
    unless edits.isEmpty do
      let text ← getFileMap
      let descriptions := edits.map fun edit =>
        let startPos := text.lspPosToUtf8Pos edit.range.start
        let endPos := text.lspPosToUtf8Pos edit.range.end
        let before := String.Pos.Raw.extract text.source startPos endPos
        s!"  `{before.trimAscii}` => `{edit.newText.trimAscii}`"
      logWarningAt stx
        m!"expected no replacements but got {edits.size}:\n{"\n".intercalate descriptions.toList}"
  | _ => throwUnsupportedSyntax

end Heron.Assert
