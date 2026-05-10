module

public meta import Heron.Rule
public meta import Lean.Server.CodeActions.Basic

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

/-- A reference to external documentation that justifies a check rule. -/
structure Reference where
  /-- Short topic description shown in parentheses, e.g. `` `rfl` tactic ``. -/
  topic : String
  /-- URL to the external documentation. -/
  url : String

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
  /-- Optional reference rendered as a markdown link in the hover popup. -/
  reference : Option Reference := none

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

/-- Emit a check diagnostic. Per-replacement and extra labels are surfaced via
`Diagnostic.relatedInformation` (patched into `BaseMessage.relatedInformation?`
upstream). The associated quick-fix is produced by `heronCheckFixProvider` via
re-detection at LSP request time, so this function no longer needs to embed
edits in `Diagnostic.data?`. -/
meta def emitCheck (node : Syntax) (severity : MessageSeverity) (tags : Array Lsp.DiagnosticTag)
    (ruleName : Name) (optName : Name) (message explanation : MessageData) (repls : Array Replacement)
    (relatedInformation : Array Lsp.DiagnosticRelatedInformation := #[])
    (reference : Option Reference := none) : CommandElabM Unit := do
  let bodyParts : Array MessageData :=
    (#[explanation] : Array MessageData)
      |>.append (match reference with
        | some ref => (#[m!"\n\nLean Reference ({ref.topic}): *{ref.url}*"] : Array MessageData)
        | none => #[])
      |>.push m!"\n\nDisable with `set_option {optName} false`"
  let composedMsg := bodyParts.foldl (init := message) fun acc part => acc ++ part
  let taggedMsg := (applyDiagnosticTags tags composedMsg).tagWithErrorName ruleName
  let ref := replaceRef node (← MonadLog.getRef)
  let pos := ref.getPos?.getD 0
  let endPos := ref.getTailPos?.getD pos
  let fileMap ← getFileMap
  let msgData ← addMessageContext taggedMsg
  let severity := if warningAsError.get (← getOptions) && severity == .warning then .error else severity
  trace[heron]"  emitting {severity} at {(fileMap.toPosition pos)}: {repls.size} replacement(s)"
  let msg : Message :=
    { fileName := ← getFileName
      pos := fileMap.toPosition pos
      endPos := fileMap.toPosition endPos
      keepFullRange := true
      data := msgData
      severity
      relatedInformation? := if relatedInformation.isEmpty then none else some relatedInformation }
  logMessage msg

/-- A live, per-command handler instance for one rule. The master linter builds
one of these per enabled rule per command, calls `visit` at every node whose
kind matches the rule, then calls `emit` once at the end. -/
structure RuleHandler where
  /-- Syntax kinds at which `visit` should be invoked. -/
  kinds : Array SyntaxNodeKind
  /-- Called once per matching node during the master walk; accumulates matches
  in handler-private state. -/
  visit : Syntax → CommandElabM Unit
  /-- Called once after the walk; emits one diagnostic per accumulated match. -/
  emit : CommandElabM Unit

/-- A type-erased registration. The registry stores `setup` thunks that build a
fresh `RuleHandler` for each command (each handler owns its own match-collection
state via `IO.Ref`), plus a `findActions` thunk used by the code-action provider
to re-detect matches at request time. -/
structure RuleEntry where
  name : Name
  isEnabled : Options → Bool
  setup : CommandElabM RuleHandler
  /-- Re-run detection over the given command syntax and return one
  `(title, replacements)` per match. Used by `heronCheckFixProvider` to build
  quick-fix code actions without embedding edits in diagnostics. -/
  findActions : Syntax → CommandElabM (Array (MessageData × Array Replacement))

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
      let fileMap ← getFileMap
      let uri : Lsp.DocumentUri := System.Uri.pathToUri (System.FilePath.mk (← getFileName))
      for m in collected do
        let repls ← Rule.replacements (α := α) m
        let related ← Rule.collectRelatedInformation (α := α) m repls fileMap uri
        emitCheck (node := Check.emphasize m) (severity := Check.severity (α := α))
            (tags := Check.tags (α := α))
            (ruleName := name) (optName := (Rule.linterOption (α := α)).name)
            (message := Rule.message m) (explanation := Check.explanation m)
            (repls := repls) (relatedInformation := related)
            (reference := Check.reference (α := α))
      let emitEnd ← IO.monoNanosNow
      if profiling then
        Heron.recordProfile name (detectEnd - walkStart) (emitEnd - detectEnd) collected.size
  }

/-- Walk `stx` once, dispatching each node to every handler that registered for
its kind. -/
private meta partial def walkDispatch
    (table : Std.HashMap SyntaxNodeKind (Array (Syntax → CommandElabM Unit))) (stx : Syntax) :
    CommandElabM Unit := do
  if let some hs := table[stx.getKind]? then
    for h in hs do h stx
  for c in stx.getArgs do walkDispatch table c

/-- Build the kind→handlers dispatch table from a list of live handlers. -/
private meta def buildDispatchTable (handlers : Array RuleHandler) :
    Std.HashMap SyntaxNodeKind (Array (Syntax → CommandElabM Unit)) :=
  handlers.foldl (init := {}) fun tbl h =>
    h.kinds.foldl (init := tbl) fun tbl k =>
      tbl.insert k ((tbl[k]?.getD #[]).push h.visit)

/-- The single linter Heron registers with Lean. It activates every enabled
rule, builds one handler per rule, walks the command syntax once via kind-keyed
dispatch, then runs each handler's emit phase. Handlers with empty `kinds`
fire once at the command root (file-level analyses like import checks). -/
meta def heronMasterLinter : Linter where
  name := `heron
  run := withSetOptionIn fun stx => do
    if Heron.isReelaboratingGuardSet (← getOptions) then return
    let opts ← getOptions
    let entries ← heronRuleRegistry.get
    let active := entries.filter (·.isEnabled opts)
    if active.isEmpty then return
    let handlers ← active.mapM (·.setup)
    for h in handlers do
      if h.kinds.isEmpty then h.visit stx
    walkDispatch (buildDispatchTable handlers) stx
    for h in handlers do h.emit

meta initialize lintersRef.modify (·.push heronMasterLinter)

/-- Re-run a `Check` rule's detection over `stx` and pair every match with its
displayable title and computed replacements. This is the read-only twin of
`Check.makeHandler`'s emit phase, used by the code-action provider. -/
private meta def Check.findActions [Check α] (stx : Syntax) :
    CommandElabM (Array (MessageData × Array Replacement)) := do
  let detected ← Rule.detectAll (α := α) stx
  detected.mapM fun m => do
    let repls ← Rule.replacements (α := α) m
    return (Rule.message (α := α) m, repls)

/-- Register a `Check` instance: linter option, registry entry, and test runner. -/
meta def Check.register [Check α] : IO Unit := do
  let name := Rule.name (α := α)
  Rule.registerLinterOption name
  heronRuleRegistry.modify fun reg =>
    (reg.filter (·.name != name)).push
      { name
        isEnabled := Rule.isEnabled (α := α)
        setup := Check.makeHandler (α := α)
        findActions := Check.findActions (α := α) }
  Rule.testRunnerRegistry.modify (·.insert name (Rule.buildTestRunner (α := α)))

open Server RequestM Lsp in
@[code_action_provider]
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
      detected.mapM fun (msg, repls) => do
        let edits ← repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
        return (msg, repls, edits)
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

end Heron
