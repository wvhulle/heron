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

/-- Emit a check diagnostic with an associated quick-fix code action. -/
meta def emitCheck (node : Syntax) (severity : MessageSeverity) (category : Category) (tags : Array Lsp.DiagnosticTag)
    (ruleName : Name) (optName : Name) (message explanation : MessageData) (repls : Array Replacement)
    (reference : Option Reference := none) : CommandElabM Unit := do
  let taggedMsg := message.tagWithErrorName ruleName
  let ref := replaceRef node (← MonadLog.getRef)
  let pos := ref.getPos?.getD 0
  let endPos := ref.getTailPos?.getD pos
  let fileMap ← getFileMap
  let msgData ← addMessageContext taggedMsg
  let severity := if warningAsError.get (← getOptions) && severity == .warning then .error else severity
  let shortFmt ← liftCoreM message.format
  let editsArr ← repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
  let edits := Json.arr (editsArr.map toJson)
  trace[heron]"  emitting {severity} at {(fileMap.toPosition pos)}: {repls.size} replacement(s)"
  let longFmt ← liftCoreM explanation.format
  let bodyParts := #[longFmt.pretty].filter (!·.isEmpty)
    |>.append (match reference with | some ref => #[s!"Lean Reference ({ref.topic}): *{ref.url}*"] | none => #[])
    |>.push s!"Disable with `set_option {optName} false`"
  let data :=
    Lean.Json.mkObj
      [("title", .str shortFmt.pretty), ("edits", edits), ("hoverTitle", .str shortFmt.pretty),
        ("hoverTags", Json.arr #[toJson (toString category)]),
        ("hoverBody", .str ("\n\n".intercalate bodyParts.toList))]
  let msg : Message :=
    { fileName := ← getFileName
      pos := fileMap.toPosition pos
      endPos := fileMap.toPosition endPos
      keepFullRange := true
      data := msgData
      severity
      diagnosticTags := tags
      diagnosticData? := some data.compress }
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
state via `IO.Ref`). -/
structure RuleEntry where
  name : Name
  isEnabled : Options → Bool
  setup : CommandElabM RuleHandler

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
      for m in collected do
        let repls ← Rule.replacements (α := α) m
        emitCheck (node := Check.emphasize m) (severity := Check.severity (α := α))
            (category := Check.category (α := α)) (tags := Check.tags (α := α))
            (ruleName := name) (optName := (Rule.linterOption (α := α)).name)
            (message := Rule.message m) (explanation := Check.explanation m)
            (repls := repls) (reference := Check.reference (α := α))
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

/-- Register a `Check` instance: linter option, registry entry, and test runner. -/
meta def Check.register [Check α] : IO Unit := do
  let name := Rule.name (α := α)
  Rule.registerLinterOption name
  heronRuleRegistry.modify fun reg =>
    (reg.filter (·.name != name)).push
      { name
        isEnabled := Rule.isEnabled (α := α)
        setup := Check.makeHandler (α := α) }
  Rule.testRunnerRegistry.modify (·.insert name (Rule.buildTestRunner (α := α)))

open Server RequestM Lsp in
@[code_action_provider]
meta def heronCheckFixProvider : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  params.context.diagnostics.filterMapM fun diag => do
    let some data := diag.data? | return none
    let some title := data.getObjValAs? String "title" |>.toOption | return none
    let some edits := data.getObjValAs? (Array TextEdit) "edits" |>.toOption | return none
    let fullAction : CodeAction :=
      { title, kind? := "quickfix"
        edit? := some <| .ofTextDocumentEdit { textDocument := doc.versionedIdentifier, edits }
        diagnostics? := some #[diag] }
    return some { eager := { fullAction with edit? := none }, lazy? := some (pure fullAction) }

end Heron
