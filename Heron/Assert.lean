module

-- Needed publicly: the `@[command_elab]`-registered elaborators below must be
-- public for the attribute to accept them, and `CommandElab` appears in their
-- signatures. Narrowing this further would require splitting the syntax
-- declarations and elaborators into separate modules.
public meta import Lean.Elab.Command
-- `public` required: referenced (via a private helper) by public
-- `@[command_elab]` elaborators. The module system checks transitively
-- through private helpers.
public meta import Heron.Rule
public meta import Heron.Lsp
public meta import Heron.Fix
-- Private: only used by the elaborator-internal helper `elabAssertResult` for
-- `Syntax.getQuotContent`, which is available without re-exporting.
meta import Lean.Elab.Quotation

public section

namespace Heron.Assert

open Lean Elab Command Heron

private meta def elabCommandSilently (cmd : Syntax) : CommandElabM Unit :=
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    withReader ({ · with snap? := none }) do
      try elabCommand cmd catch _ => pure ()

/-- Run a rule against a command for testing.

Looks up the rule's runner by name and calls it directly — the same
`Rule.detect` + `Rule.replacements` + `Replacement.toTextEdit?` path
used by the code action providers. Returns both the detection count and
the resulting text edits so callers can distinguish "rule did not fire"
from "rule fired but produced no automatic fix". -/
private meta def runRule (cmd : Syntax) (linterName : Name)
    : CommandElabM RunResult := do
  let runners ← testRunnerRegistry.get
  let some runner := runners[linterName]? | do
    throwError "no rule runner registered for '{linterName}'"
  -- Elaborate the command so that rules needing info trees can find them.
  -- Save and restore messages to suppress any diagnostics from elaboration.
  withScope (fun scope => { scope with opts := scope.opts.insert (`linter ++ linterName) (.ofBool true) }) do
    let savedMessages := (← get).messages
    withoutModifyingEnv do
      elabCommandSilently cmd
      let result ← runner cmd
      modify fun s => { s with messages := savedMessages }
      pure result

-- `applyEdits` (used below) is shared from `Heron.Fix` (opened via `open … Heron`).

/-- Verify that a rule fires on `cmd`, optionally checking that applying all
its edits produces the text in `expectedQuot?`. When `expectedQuot?` is
`none`, the assertion is satisfied as long as `Rule.detect` produced at
least one match — used for warning-only rules with no automatic fix. -/
private meta def elabAssertResult (linterName : Ident) (cmd : Syntax)
    (expectedQuot? : Option Syntax) (stx : Syntax) : CommandElabM Unit := do
  let { matchCount, edits } ← runRule cmd linterName.getId
  if matchCount == 0 then
    logErrorAt stx m!"{linterName} did not fire on this command"
    return
  let some expectedQuot := expectedQuot? | return
  if edits.isEmpty then
    logErrorAt stx
      m!"{linterName} fired but produced no replacements; drop `becomes` or \
         add a `replacements` implementation"
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
  -- Normalize both expected and actual through Lean's pretty printer
  let expectedNorm ← try
    let fmt ← liftCoreM <| PrettyPrinter.ppCategory `command expectedQuot.getQuotContent
    pure fmt.pretty
  catch _ =>
    let some text := expectedQuot.getQuotContent.reprint
      | do logWarningAt stx m!"could not reprint expected quotation"; return
    pure text.trimAscii.toString
  let actualNorm ← try
    match Parser.runParserCategory (← getEnv) `command actual with
    | .ok stx' =>
      let fmt ← liftCoreM <| PrettyPrinter.ppCategory `command stx'
      pure fmt.pretty
    | .error _ => pure actual.trimAscii.toString
  catch _ => pure actual.trimAscii.toString
  unless actualNorm == expectedNorm do
    logErrorAt stx
      m!"\n\n{linterName} failed to rewrite:\n\noriginal:\n{original.trimAscii}\n\nexpected:\n{expectedNorm}\n\nactual:\n{actualNorm}\n"

syntax (name := assertCheckCmd)
  "#assertCheck " ident " in " command (" becomes " term)? : command

syntax (name := assertRefactorCmd)
  "#assertRefactor " ident " in " command " becomes " term : command

@[command_elab assertCheckCmd] meta def elabAssertCheck : CommandElab
  | stx@`(command| #assertCheck $linterName in $cmd becomes $expected) => do
    elabAssertResult linterName cmd (some expected) stx
  | stx@`(command| #assertCheck $linterName in $cmd) => do
    elabAssertResult linterName cmd none stx
  | _ => throwUnsupportedSyntax

@[command_elab assertRefactorCmd] meta def elabAssertRefactor : CommandElab
  | stx@`(command| #assertRefactor $linterName in $cmd becomes $expected) => do
    elabAssertResult linterName cmd (some expected) stx
  | _ => throwUnsupportedSyntax

syntax (name := assertIgnoreCmd)
  "#assertIgnore " ident " in " command : command

@[command_elab assertIgnoreCmd] meta def elabAssertIgnore : CommandElab
  | stx@`(command| #assertIgnore $linterName in $cmd) => do
    let { edits, .. } ← runRule cmd linterName.getId
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
