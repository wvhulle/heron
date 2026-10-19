module

public meta import Heron.Rule
public meta import Heron.Monad
public meta import Heron.Lsp
public meta import Heron.Fix
public meta import Lean.Server.CodeActions.Basic
-- `withSetOptionIn` lives in `Lean.Linter.Basic`; under newer toolchains it is no
-- longer pulled in transitively, so import it directly (see `heronMasterLinter`).
meta import Lean.Linter.Basic
meta import Lean.Elab.BuiltinTerm

public section

open Lean Elab Command Meta

namespace Heron

/-- Category classifying the kind of pattern a check reports. -/
inductive Category where
| style
| simplification
| performance
| correctness
  deriving Inhabited, BEq

meta instance : ToString Category where
  toString
    | .style => "style"
    | .simplification => "simplification"
    | .performance => "performance"
    | .correctness => "correctness"

private meta def positionalSyntaxAccessors : Array Name :=
  #[``Lean.Syntax.getArg, ``Lean.Syntax.getArgs, ``Lean.Syntax.getNumArgs, ``Lean.Syntax.getIdAt]

private meta def indexingFunctions : Array Name :=
  #[``GetElem.getElem, ``GetElem?.getElem?, ``GetElem?.getElem!]

private meta def indexesIntoSyntax (e : Expr) : Bool :=
  indexingFunctions.any e.isAppOf && e.getAppArgs[0]?.any (·.isConstOf ``Lean.Syntax)

meta def isPositionalSyntaxAccess (e : Expr) : Bool :=
  positionalSyntaxAccessors.any e.getAppFn.isConstOf || indexesIntoSyntax e

private meta def isApplicationSyntax : Syntax → Bool
  | `($_:term $_*) => true
  | _ => false

private meta def termInfosOutsideNameLiterals (tree : InfoTree) : Array (ContextInfo × TermInfo) :=
  let collect : StateM (Array (ContextInfo × TermInfo)) Unit :=
    tree.visitM' (preNode := fun ci info _ => do
      let .ofTermInfo ti := info | return true
      if ti.elaborator == ``Lean.Elab.Term.elabDoubleQuotedName then return false
      modify (·.push (ci, ti))
      return true)
  (collect.run #[]).2

private meta def originalTermInfosWithin (node : Syntax) (keep : Syntax → Bool) (isTarget : Expr → Bool) :
    CommandElabM (Array Syntax) := do
  let some range := node.getRange? | return #[]
  let trees ← collectInfoTrees node
  let hits ← (trees.flatMap termInfosOutsideNameLiterals).filterM fun (ci, ti) => do
    let .original .. := ti.stx.getHeadInfo | return false
    unless ti.stx.getRange?.any fun r => range.start ≤ r.start && r.stop ≤ range.stop do return false
    unless keep ti.stx do return false
    runInfoMetaM ci ti.lctx do return isTarget (← instantiateMVars ti.expr)
  return (deduplicateTermInfos hits).map (·.2.stx)

meta def originalCallSitesOf (node : Syntax) (isTarget : Expr → Bool) : CommandElabM (Array Syntax) :=
  originalTermInfosWithin node (!isApplicationSyntax ·) isTarget

meta def originalApplicationsOf (node : Syntax) (isTarget : Expr → Bool) : CommandElabM (Array Syntax) :=
  originalTermInfosWithin node isApplicationSyntax isTarget

class Check (α : Type) extends Rule α where
  /-- Diagnostic severity. -/
  severity : MessageSeverity
  /-- What kind of pattern this rule detects. -/
  category : Category
  /-- Syntax node whose range is underlined in the diagnostic. -/
  emphasize : α → Syntax
  /-- LSP diagnostic tags (e.g. unnecessary, deprecated) applied to the match range. -/
  tags : Array Lsp.DiagnosticTag := #[]
  /-- Detailed explanation shown in hover popup. -/
  explanation : α → MessageData := fun _ => m!""

/-- Wrap `MessageData` with the upstream tag names that
`Lean.Widget.InteractiveDiagnostic` recognises and translates into LSP
`DiagnosticTag`s. This lets Heron emit `unnecessary`/`deprecated` tags via
stock Lean message infrastructure, with no patch to `Lean.Message`. -/
meta def applyDiagnosticTags (tags : Array Lsp.DiagnosticTag) (msg : MessageData) : MessageData :=
  tags.foldl (init := msg) fun acc tag =>
    match tag with
    -- Tag names recognised by `Lean.Widget.InteractiveDiagnostic`:
    -- the option name `Lean.Linter.linter.unusedVariables` → LSP `unnecessary`,
    -- the attribute `Lean.Linter.deprecatedAttr` → LSP `deprecated`.
    | .unnecessary => MessageData.tagged `Lean.Linter.linter.unusedVariables acc
    | .deprecated  => MessageData.tagged `Lean.Linter.deprecatedAttr acc

/-- Emit a check diagnostic. The published `Diagnostic.message` carries only the
short headline. The explanation / sources / disable hint are packed into
`Diagnostic.data?` as `DiagnosticHoverData`, which Lean's hover handler renders
into the hover popup at request time.

The associated quick-fix is produced by `heronCheckFixProvider` via re-detection
at LSP request time. Per-replacement labels and any extra labels flow into
`Diagnostic.relatedInformation` via the patched `BaseMessage.relatedInformation?`. -/
meta def emitCheck (node : Syntax) (severity : MessageSeverity) (tags : Array Lsp.DiagnosticTag)
    (ruleName : Name) (optName : Name) (message explanation : MessageData)
    (sources : Array Source := #[]) : CommandElabM Unit := do
  let taggedMsg := applyDiagnosticTags tags message
  let ref := replaceRef node (← MonadLog.getRef)
  let pos := ref.getPos?.getD 0
  let endPos := ref.getTailPos?.getD pos
  let fileMap ← getFileMap
  let sourcesMd : MessageData := sources.foldl (init := m!"") fun acc source =>
    let link := source.toLink
    acc ++ m!"**Source ({link.title}):** {link.url}\n\n"
  let disableMd : MessageData := m!"_Disable with `set_option {optName} false`._"
  -- Stock Lean has no `Message.diagnosticData?` channel for a separate hover
  -- popup (a fork-only extension), so fold the explanation / sources / disable
  -- hint directly into the published diagnostic message instead.
  let body : MessageData :=
    taggedMsg ++ m!"\n\n" ++ explanation ++ m!"\n\n" ++ sourcesMd ++ disableMd
  let msgData ← addMessageContext (body.tagWithErrorName (lspName ruleName))
  let severity := if warningAsError.get (← getOptions) && severity == .warning then .error else severity
  let msg : Message :=
    { fileName := ← getFileName
      pos := fileMap.toPosition pos
      endPos := fileMap.toPosition endPos
      keepFullRange := true
      data := msgData
      severity }
  logMessage msg

/-- Emit one `.information`-severity diagnostic per label so that LSP clients
that don't render `relatedInformation` (notably Helix) still surface the label
text inline at the labelled span. The label's range is excluded if it would
overlap or duplicate an existing replacement's `oldSyntax` range — those are
already underlined by the primary diagnostic, so an extra hint there is noise.

This mirrors `nu-lint`'s `extra_labels_to_hint_diagnostics`. -/
private meta def emitLabelHints (ruleName : Name) (primaryRange? : Option Syntax.Range)
    (replacementRanges : Array Syntax.Range) (labels : Array Label) : CommandElabM Unit := do
  let fileMap ← getFileMap
  let mut seen : Array Syntax.Range := primaryRange?.toArray ++ replacementRanges
  for l in labels do
    let some range := l.span.getRange? | continue
    if seen.any fun r => r.start = range.start ∧ r.stop = range.stop then continue
    seen := seen.push range
    let pos := fileMap.toPosition range.start
    let endPos := fileMap.toPosition range.stop
    let labelData ← addMessageContext ((l.text).tagWithErrorName (lspName ruleName))
    logMessage {
      fileName := ← getFileName
      pos
      endPos
      keepFullRange := true
      data := labelData
      severity := .information
    }

/-- A live, per-command handler instance for one rule. The master linter builds
one of these per enabled rule per command, calls `visit` at every node whose
kind matches the rule, then calls `emit` once at the end. -/
structure RuleHandler where
  /-- Syntax kinds at which `visit` should be invoked. -/
  kinds : Array SyntaxNodeKind
  within : Array SyntaxNodeKind
  /-- Called once per matching node during the master walk; accumulates matches
  in handler-private state. -/
  visit : Syntax → CommandElabM Unit
  /-- Called once after the walk; emits one diagnostic per accumulated match. -/
  emit : CommandElabM Unit

/-- A type-erased registration. The registry stores `setup` thunks that build a
fresh `RuleHandler` for each command (each handler owns its own match-collection
state via `IO.Ref`), plus a `findActions` thunk used by the code-action provider
to re-detect matches at request time. -/
structure Finding where
  message : MessageData
  explanation : MessageData
  emphasized : Syntax
  replacements : Array Replacement

structure RuleEntry where
  name : Name
  isEnabled : Options → Bool
  setup : CommandElabM RuleHandler
  /-- Re-run detection over the given command syntax and return one `Finding` per match.
  Used by `heronCheckFixProvider` to build quick-fix code actions and by
  `collectFixRecords` to carry the hover-popup explanation into the CLI's `FixRecord`. -/
  findActions : Syntax → CommandElabM (Array Finding)
  sources : Array Source

meta initialize heronRuleRegistry : IO.Ref (Array RuleEntry) ← IO.mkRef #[]

/-- Build a fresh `RuleHandler` for one `Check` rule for one command.

When `Rule.consumesSubtree` is `true`, the visit closure tracks ranges of
nodes where `detect` produced matches and short-circuits at any descendant of
those ranges. Because the shared dispatch walk is preorder, ancestors are
always visited before their descendants, so a flat array of consumed ranges
filters descendants without a second pass. -/
private meta def Check.makeHandler [Check α] : CommandElabM RuleHandler := do
  let matchesRef ← IO.mkRef (#[] : Array α)
  let consumedRef ← IO.mkRef (#[] : Array Lean.Syntax.Range)
  let consumes := Rule.consumesSubtree (α := α)
  let name := Rule.name (α := α)
  let profiling := Heron.isProfilingEnabled (← getOptions)
  let walkStart ← IO.monoNanosNow
  return {
    kinds := Rule.kinds (α := α)
    within := Rule.within (α := α)
    visit := fun node => do
      if consumes then
        if let some r := node.getRange? then
          if (← consumedRef.get).any fun c => c.start ≤ r.start ∧ r.stop ≤ c.stop then
            return
      let found ← Rule.detect (α := α) node
      if found.isEmpty then return
      matchesRef.modify (· ++ found)
      if consumes then
        if let some r := node.getRange? then
          consumedRef.modify (·.push r)
    emit := do
      let collected ← matchesRef.get
      let detectEnd ← IO.monoNanosNow
      for m in collected do
        let repls ← Rule.replacementsFor m
        emitCheck (node := Check.emphasize m) (severity := Check.severity (α := α))
            (tags := Check.tags (α := α))
            (ruleName := name) (optName := (Rule.linterOption (α := α)).name)
            (message := Rule.message m) (explanation := Check.explanation m)
            (sources := Rule.sources (α := α))
        let primaryRange? := (Check.emphasize m).getRange?
        let replacementRanges := repls.filterMap (·.oldSyntax.getRange?)
        let extraLabels ← Rule.labels (α := α) m
        let allLabels := repls.map (·.toLabel) ++ extraLabels
        emitLabelHints name primaryRange? replacementRanges allLabels
      let emitEnd ← IO.monoNanosNow
      if profiling then
        Heron.recordProfile name (detectEnd - walkStart) (emitEnd - detectEnd) collected.size
  }

/-- Walk `stx` once, dispatching each node to every handler that registered for
its kind. -/
private meta partial def walkDispatch
    (table : Std.HashMap SyntaxNodeKind (Array RuleHandler)) (enclosingKinds : Array SyntaxNodeKind)
    (stx : Syntax) : CommandElabM Unit := do
  let enclosingKinds := enclosingKinds.push stx.getKind
  if let some hs := table[stx.getKind]? then
    for h in hs do
      if h.within.isEmpty || enclosingKinds.any h.within.contains then h.visit stx
  for c in stx.getArgs do walkDispatch table enclosingKinds c

/-- Build the kind→handlers dispatch table from a list of live handlers. -/
private meta def buildDispatchTable (handlers : Array RuleHandler) :
    Std.HashMap SyntaxNodeKind (Array RuleHandler) :=
  handlers.foldl (init := {}) fun tbl h =>
    h.kinds.foldl (init := tbl) fun tbl k =>
      tbl.insert k ((tbl[k]?.getD #[]).push h)

/-- Run `checks` against `cmd` and return a `FixRecord` per suggested replacement —
the same `findActions` → `Replacement.toTextEdit` path the code-action provider uses. Each check
is still gated by `isEnabled`; with `all := true` the manual **refactors** (`testRunnerRegistry`
entries that aren't checks) are added too. Shared by the build sink (below) and the standalone
`heron-scan` driver. -/
meta def collectFixRecords (all : Bool) (checks : Array RuleEntry) (stx : Syntax) :
    CommandElabM (Array FixRecord) := do
  let fileMap ← getFileMap
  let opts ← getOptions
  let checkNames := (← heronRuleRegistry.get).map (·.name)
  let mut out : Array FixRecord := #[]
  for entry in checks do
    if entry.isEnabled opts then
      let links := entry.sources.map (·.toLink)
      for finding in (← entry.findActions stx) do
        let title := (← finding.message.toString).trimAscii.toString
        let explStr := (← finding.explanation.toString).trimAscii.toString
        let edits ← finding.replacements.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
        if edits.isEmpty then
          let some range := finding.emphasized.getRange? | continue
          out := out.push { rule := entry.name.toString, message := title,
                            span := fileMap.utf8RangeToLspRange range, explanation := explStr, sources := links }
        for edit in edits do
          out := out.push { rule := entry.name.toString, message := title, span := edit.range,
                            edit := some edit, explanation := explStr, sources := links }
  if all then
    let runners ← testRunnerRegistry.get
    for (name, runner) in runners.toList do
      unless checkNames.contains name do
        for edit in (← runner stx).edits do
          out := out.push { rule := name.toString, message := "", span := edit.range, edit := some edit }
  return out

/-- Per-module accumulator of fix records. One `lean` process builds one module, so a single
process-global ref suffices; it is (re)written to the sink as the linter runs. -/
meta initialize heronFixAccum : Std.Mutex (Array FixRecord) ← Std.Mutex.new #[]

/-- Append this command's fixes to `<dir>/<module>.json`, turning a normal `lake build` into a
fix-collecting pass (consumed by the `heron` reporter). `dir` defaults to `.lake/build/heron-fixes`
(overridable with `HERON_FIX_DIR`), so an always-on plugin build keeps the sink in sync with the
oleans as a side effect of elaboration — the reporter then just reads it, with no re-elaboration.
Runs against the build's live elaboration; the file is rewritten on each command (the first
truncates any stale content) and stamped with the source hash for freshness checks. This runs only
inside the linter, i.e. only when `linter.heron` is enabled. -/
private meta def writeFixSink (stx : Syntax) : CommandElabM Unit := do
  let dir := (← IO.getEnv "HERON_FIX_DIR").getD ".lake/build/heron-fixes"
  let recs ← collectFixRecords (all := false) (← heronRuleRegistry.get) stx
  let mod ← getMainModule
  let sourceHash := (hash (← getFileMap).source).toNat
  heronFixAccum.atomically (m := IO) do
    modify (· ++ recs)
    let all ← get
    let payload := Json.mkObj
      [ ("source", (sourceHash : Nat)), ("fixes", Json.arr (all.map (toJson ·))) ]
    try
      IO.FS.createDirAll dir
      IO.FS.writeFile (System.FilePath.mk dir / s!"{mod}.json") payload.compress
    catch _ => pure ()

/-- The single linter Heron registers with Lean. It activates every enabled
rule, builds one handler per rule, walks the command syntax once via kind-keyed
dispatch, then runs each handler's emit phase. Finally, `writeFixSink` records
the fixes when `HERON_FIX_DIR` is set. -/
private meta def heronMasterLinter : Linter where
  name := `heron
  run := withSetOptionIn fun stx => do
    if Heron.isReelaboratingGuardSet (← getOptions) then return
    let opts ← getOptions
    let entries ← heronRuleRegistry.get
    let active := entries.filter (·.isEnabled opts)
    if active.isEmpty then return
    let handlers ← active.mapM (·.setup)
    walkDispatch (buildDispatchTable handlers) #[] stx
    for h in handlers do h.emit
    writeFixSink stx

meta initialize lintersRef.modify (·.push heronMasterLinter)

/-- Re-run a `Check` rule's detection over `stx` and pair every match with its
displayable title and computed replacements. This is the read-only twin of
`Check.makeHandler`'s emit phase, used by the code-action provider. -/
private meta def Check.findActions [Check α] (stx : Syntax) : CommandElabM (Array Finding) := do
  let detected ← Rule.detectAll (α := α) stx
  detected.mapM fun m => do
    return { message := Rule.message (α := α) m, explanation := Check.explanation (α := α) m,
             emphasized := Check.emphasize (α := α) m, replacements := ← Rule.replacementsFor m }

/-- Register a `Check` instance: linter option, registry entry, and test runner. -/
meta def Check.register [Check α] : IO Unit := do
  let name := Rule.name (α := α)
  if (← heronRuleRegistry.get).any (·.name == name) then
    throw <| IO.userError s!"Heron: two checks are registered under the name `{name}`"
  registerLinterOption name
  heronRuleRegistry.modify fun reg =>
    reg.push
      { name
        isEnabled := Rule.isEnabled (α := α)
        setup := Check.makeHandler (α := α)
        findActions := Check.findActions (α := α)
        sources := Rule.sources (α := α) }
  ruleCatalog.modify fun catalog =>
    catalog.push
      { name
        kind := .check
        description := Rule.description (α := α)
        sources := Rule.sources (α := α)
        offersFix := Rule.offersFix (α := α) }
  testRunnerRegistry.modify (·.insert name (buildTestRunner (α := α)))

open Server RequestM Lsp in
meta def heronCheckFixProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let startPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  let allEntries ← heronRuleRegistry.get
  let collect : CommandElabM (Array (MessageData × Array Replacement × Array TextEdit)) := do
    let fileMap ← getFileMap
    let opts ← getOptions
    let entries := allEntries.filter (·.isEnabled opts)
    entries.flatMapM fun entry => do
      let detected ← entry.findActions snap.stx
      detected.mapM fun finding => do
        let edits ← finding.replacements.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
        return (finding.message, finding.replacements, edits)
  let results ← runCommandElabM snap collect
  let overlaps (r : Replacement) := match r.emphasizedSyntax.getRange? with
    | some range => range.start ≤ endPos && startPos ≤ range.stop
    | none => false
  let rangeMatches (r : Replacement) (diag : Diagnostic) : Bool :=
    match r.emphasizedSyntax.getRange? with
    | some range =>
      let lspRange := text.utf8RangeToLspRange range
      lspRange.start == diag.range.start && lspRange.end == diag.range.end
    | none => false
  results.filterMapM fun (msg, repls, edits) => do
    unless repls.any overlaps do return none
    if edits.isEmpty then return none
    let title := (← msg.format).pretty
    let diagnostics? :=
      let matched := params.context.diagnostics.filter fun d => repls.any (rangeMatches · d)
      if matched.isEmpty then none else some matched
    let full : CodeAction :=
      { title, kind? := "quickfix"
        edit? := some <| .ofTextDocumentEdit { textDocument := doc.versionedIdentifier, edits }
        diagnostics? }
    return some { eager := { full with edit? := none }, lazy? := some (pure full) }

meta initialize Server.addBuiltinCodeActionProvider (lspName `quickFix) heronCheckFixProvider

end Heron
