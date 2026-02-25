import Lean.Elab.Command
import Lean.Meta.Hint
import Lean.Server.InfoUtils

open Lean Elab Command Meta

namespace Heron.Provider

/-- A single text replacement with associated source annotation. -/
structure Replacement where
  /-- Syntax node to underline in the diagnostic or anchor the code action. -/
  sourceNode : Syntax
  /-- Syntax node whose range is replaced by `insertText`. -/
  targetNode : Syntax
  /-- Text inserted in place of `targetNode`. -/
  insertText : String
  /-- Inline label shown below the span in editors. -/
  sourceLabel : MessageData

/-- Convert to a `Hint.Suggestion` for the try-this widget. -/
def Replacement.toSuggestion (r : Replacement) : Hint.Suggestion :=
  { suggestion := r.insertText, span? := some r.targetNode }

/-- Convert to an LSP `TextEdit`, if the target node has a source range. -/
def Replacement.toTextEdit? (r : Replacement) (fileMap : FileMap) : Option Lsp.TextEdit := do
  let range ← r.targetNode.getRange?
  return { range := fileMap.utf8RangeToLspRange range, newText := r.insertText }

class Transform (α : Type) where
  /-- Rule name, used to derive the linter option `linter.<name>`. -/
  ruleName : Name
  /-- Detect violations, returning typed fix data. -/
  detect : Syntax → CommandElabM (Array α)
  /-- Hint message shown alongside the suggestion widget. -/
  hintMessage : α → MessageData
  /-- Per-edit replacement data. -/
  replacements : α → Array Replacement

def Transform.option [Transform α] : Lean.Option Bool :=
  { name := `linter ++ Transform.ruleName (α := α), defValue := false }

def Transform.initOption [Transform α] : IO Unit :=
  Lean.registerOption (`linter ++ Transform.ruleName (α := α))
    { defValue := .ofBool false
      descr := s! "Enable the {Transform.ruleName (α := α)} linter rule."
      name := `linter }

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

/-- Get existing info trees when available (LSP code action requests),
falling back to re-elaboration when empty (e.g. `#assertEdits` test flow). -/
def collectInfoTrees (stx : Syntax) : CommandElabM (Array InfoTree) := do
  let existing := (← getInfoState).trees
  if existing.isEmpty then
    collectElabInfoTrees stx
  else
    return existing.toArray

/-- Extract `(ContextInfo × TermInfo)` pairs from an info tree. -/
def collectTermInfos (tree : InfoTree) : Array (ContextInfo × TermInfo) :=
  tree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofTermInfo ti => acc.push (ctx, ti)
    | _ => acc

/-- Deduplicate term infos sharing a start position, keeping the most applied.

Lean's elaborator produces multiple `TermInfo` nodes for the same source
position at different application depths (e.g. `f`, `f x`, `f x y`).
This keeps only the most-applied version per position. -/
def deduplicateTermInfos (infos : Array (ContextInfo × TermInfo)) : Array (ContextInfo × TermInfo) :=
  infos.foldl (init := #[]) fun acc (ci, ti) =>
    match ti.stx.getPos? true with
    | some pos =>
      match acc.findIdx? fun (_, old) => old.stx.getPos? true == some pos with
      | some idx =>
        match acc[idx]? with
        | some (_, old) =>
          if ti.expr.getAppNumArgs > old.expr.getAppNumArgs
          then acc.modify idx (fun _ => (ci, ti))
          else acc
        | none => acc
      | none => acc.push (ci, ti)
    | none => acc

/-- Run `MetaM` inside a `ContextInfo` context. -/
def runInfoMetaM (ci : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
  match ← (ci.runMetaM lctx x).toBaseIO with
  | .ok a =>
    return a
  | .error e =>
    throwError "{e}"

/-- Find the `declId` node in a command syntax tree. -/
partial def findDeclId? : Syntax → Option Syntax
  | stx@(.node _ kind args) =>
    if kind == ``Lean.Parser.Command.declId then some stx
    else args.findSome? findDeclId?
  | _ => none

/-- Get the source range of the `declId` in a command, if any. -/
def getDeclIdRange? (stx : Syntax) : Option Syntax.Range :=
  (findDeclId? stx).bind (·.getRange?)

/-- Check whether a `TermInfo` lies outside the declaration-id range. -/
def outsideDeclId (declRange? : Option Syntax.Range) (ti : TermInfo) : Bool :=
  match declRange?, ti.stx.getPos? with
  | some r, some p => !r.contains p
  | _, _ => true

/-- Pretty-print an expression inside a `ContextInfo`, returning a parenthesised string. -/
def ppExprFix? (ci : ContextInfo) (lctx : LocalContext) (e : Expr)
    : CommandElabM (Option String) := do
  try
    let fmt ← runInfoMetaM ci lctx (ppExpr e)
    return some s!"({fmt})"
  catch _ => return none

end Heron.Provider
