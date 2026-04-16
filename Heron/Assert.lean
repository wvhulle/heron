module

-- Needed publicly: the `@[command_elab]`-registered elaborators below must be
-- public for the attribute to accept them, and `CommandElab` appears in their
-- signatures. Narrowing this further would require splitting the syntax
-- declarations and elaborators into separate modules.
public meta import Lean.Elab.Command
-- `public` required: referenced (via a private helper) by public
-- `@[command_elab]` elaborators. The module system checks transitively
-- through private helpers.
public meta import Heron.TestRunner
public meta import Heron.ImportAnalysis
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

/-- Collect all `TextEdit`s produced by a rule for a command.

Looks up the rule's runner by name and calls it directly — the same
`Rule.detect` + `Rule.replacements` + `Replacement.toTextEdit?` path
used by the code action providers. -/
private meta def collectReplacements (cmd : Syntax) (linterName : Name)
    : CommandElabM (Array Lsp.TextEdit) := do
  let runners ← Rule.testRunnerRegistry.get
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
      pure edits

/-- Apply an array of non-overlapping LSP `TextEdit`s to a source string.

Edits are sorted by range start descending and applied back-to-front so that
earlier byte offsets remain valid, matching the LSP specification that all
ranges refer to the original document. -/
private meta def applyEdits (text : FileMap) (edits : Array Lsp.TextEdit) : String :=
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
private meta def elabAssertResult (linterName : Ident) (cmd : Syntax)
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

/-- Record `Heron.Assert` as an implicit dependency of the current file so the
unused-import analysis counts it as used whenever any of the `#assert*`
commands below are invoked. This removes the need for consumers to write a
dummy `_usedAssert := @Heron.Assert.applyEdits` reference. -/
private meta def recordAssertUsage : CommandElabM Unit :=
  Lean.recordExtraModUse `Heron.Assert (isMeta := true)

syntax (name := assertCheckCmd)
  "#assertCheck " ident " in " command " becomes " term : command

syntax (name := assertRefactorCmd)
  "#assertRefactor " ident " in " command " becomes " term : command

@[command_elab assertCheckCmd] meta def elabAssertCheck : CommandElab
  | stx@`(command| #assertCheck $linterName in $cmd becomes $expected) => do
    recordAssertUsage
    elabAssertResult linterName cmd expected stx
  | _ => throwUnsupportedSyntax

@[command_elab assertRefactorCmd] meta def elabAssertRefactor : CommandElab
  | stx@`(command| #assertRefactor $linterName in $cmd becomes $expected) => do
    recordAssertUsage
    elabAssertResult linterName cmd expected stx
  | _ => throwUnsupportedSyntax

syntax (name := assertIgnoreCmd)
  "#assertIgnore " ident " in " command : command

@[command_elab assertIgnoreCmd] meta def elabAssertIgnore : CommandElab
  | stx@`(command| #assertIgnore $linterName in $cmd) => do
    recordAssertUsage
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

/-! ## Import analysis assertion

Verify that `ImportAnalysis.analyzeImports` classifies the current file's
imports exactly as expected. Unlike `#assertCheck`, this operates on the
file's own header — so the assertion must be the last command and each
test scenario needs its own file. -/

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
  recordAssertUsage
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
