import Lean.Elab.Command
import Lean.Meta.Hint
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta

namespace Heron

/-- Internal option to prevent recursive linter invocation during re-elaboration. -/
private def heronReelaborating : Lean.Option Bool :=
  { name := `heron.reelaborating, defValue := false }

initialize
  Lean.registerOption `heron.reelaborating {
    defValue := .ofBool false
    descr := "Internal: set during re-elaboration to prevent recursive linter invocation."
    name := `heron
  }

/-- Check whether the `heron.reelaborating` flag is set in the current options. -/
def isReelaborating (opts : Options) : Bool :=
  heronReelaborating.get opts

/-- Re-elaborate a command collecting info trees.

Uses the scoped `heron.reelaborating` option instead of clearing the global
`lintersRef` to prevent recursive linter invocation. This is safe under
concurrent (async) elaboration — `withScope` modifies only the current
command's options, so other commands' linters are unaffected. -/
def collectElabInfoTrees (stx : Syntax) : CommandElabM (Array InfoTree) := do
  let savedInfoState ← getInfoState
  let savedMessages := (← get).messages
  setInfoState { enabled := true, trees := { } }
  try
    withoutModifyingEnv do
        withScope (fun scope =>
          let opts := heronReelaborating.set (Elab.async.set scope.opts false) true
          { scope with opts }) do
            withReader ({ · with snap? := none }) do
                elabCommand stx
  catch _ =>
    pure ()
  let trees := (← getInfoState).trees.toArray
  setInfoState savedInfoState
  modify fun s => { s with messages := savedMessages }
  return trees

/-- Emit a diagnostic message with an associated quick-fix suggestion.

Constructs the `Hint.Suggestion`, builds the tagged `MessageData` with hint
and disable note, creates the `Message` with positions/tags/diagnosticData,
and calls `logMessage`. -/
def emitDiagnostic (diagNode replacementNode : Syntax)
    (severity : MessageSeverity) (diagnosticTags : Array Lsp.DiagnosticTag)
    (ruleName : Name) (optName : Name)
    (diagnosticMsg hintMsg : MessageData) (replacementText : String)
    : CommandElabM Unit := do
  let sugg : Hint.Suggestion :=
    { suggestion := replacementText
      span? := some replacementNode }
  let hint ← liftCoreM <|
    MessageData.hint hintMsg #[sugg]
  let disable := MessageData.note m!"This linter can be disabled with `set_option {optName} false`"
  let taggedMsg := MessageData.tagged optName
    m!"{diagnosticMsg ++ hint}{disable}"
  let ref := replaceRef diagNode (← MonadLog.getRef)
  let pos := ref.getPos?.getD 0
  let endPos := ref.getTailPos?.getD pos
  let fileMap ← getFileMap
  let msgData ← addMessageContext taggedMsg
  let severity :=
    if warningAsError.get (← getOptions) && severity == .warning
    then .error else severity
  let msg : Message := {
    fileName := ← getFileName
    pos := fileMap.toPosition pos
    endPos := fileMap.toPosition endPos
    data := msgData
    severity
    diagnosticTags
  }
  let refStx := sugg.span?.getD diagNode
  let msg := match refStx.getRange? with
    | some range =>
      let lspRange := fileMap.utf8RangeToLspRange range
      let newText := match sugg.suggestion with
        | .string s => s
        | .tsyntax t => t.raw.reprint.getD ""
      let data := Lean.Json.mkObj [
        ("title", .str s!"Apply: {ruleName}"),
        ("edit", toJson ({ range := lspRange, newText : Lsp.TextEdit }))
      ]
      { msg with diagnosticData? := some data.compress }
    | none => msg
  logMessage msg

open Server RequestM Lsp in
@[code_action_provider]
def heronFixProvider : CodeActionProvider := fun params _snap => do
  let doc ← readDoc
  let mut actions : Array LazyCodeAction := #[]
  for diag in params.context.diagnostics do
    let some data := diag.data? | continue
    let some title := data.getObjValAs? String "title" |>.toOption | continue
    let some edit := (do
      let ej ← data.getObjVal? "edit" |>.toOption
      fromJson? (α := TextEdit) ej |>.toOption) | continue
    let fullAction : CodeAction := {
      title
      kind? := "quickfix"
      edit? := some <| .ofTextEdit doc.versionedIdentifier edit
      diagnostics? := some #[diag]
    }
    actions := actions.push {
      eager := { fullAction with edit? := none }
      lazy? := some (pure fullAction)
    }
  return actions

end Heron
