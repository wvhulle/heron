module

public meta import Heron.Rule
public meta import Lean.Server.CodeActions.Basic
meta import Lean.Elab.Term.TermElabM

public section

open Lean Elab Command Meta

open Lean Elab Term Meta in
/-- Try to set a struct field that may only exist in a fork of Lean.
Elaborates `{ msg with field := val }`; returns `msg` unchanged on standard Lean. -/
elab "tryStructUpdate(" msg:term ", " field:ident ", " val:term ")" : term => do
  let msgExpr ← elabTerm msg none
  let msgType ← whnf (← inferType msgExpr)
  let structName := msgType.getAppFn.constName?.getD .anonymous
  let env ← getEnv
  if isStructure env structName && (getStructureFields env structName).contains field.getId then
    elabTerm (← `({ $msg with $field:ident := $val })) none
  else
    return msgExpr

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
  let msg : Message :=
    { fileName := ← getFileName
      pos := fileMap.toPosition pos
      endPos := fileMap.toPosition endPos
      keepFullRange := true
      data := msgData
      severity }
  let msg := tryStructUpdate(msg, diagnosticTags, tags)
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
  let msg := tryStructUpdate(msg, diagnosticData?, some data.compress)
  logMessage msg

meta def Check.toLinter [Check α] : Linter where
  name := Rule.name (α := α)
  run :=
    withSetOptionIn fun stx =>
      Rule.runIfEnabled (α := α) stx fun m => do
        let repls ← Rule.replacements m
        emitCheck (node := emphasize m) (severity := Check.severity (α := α)) (category := Check.category (α := α))
            (tags := Check.tags (α := α)) (ruleName := Rule.name (α := α))
            (optName := (Rule.linterOption (α := α)).name) (message := Rule.message m)
            (explanation := Check.explanation m) (repls := repls) (reference := Check.reference (α := α))

/-- Register a `Check` instance: linter option, linter, and test runner.
Called from `meta initialize` in each rule file. -/
meta def Check.register [Check α] : IO Unit := do
  let name := Rule.name (α := α)
  Rule.registerLinterOption name
  lintersRef.modify fun ls => (ls.filter (·.name != name)).push (Check.toLinter (α := α))
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
