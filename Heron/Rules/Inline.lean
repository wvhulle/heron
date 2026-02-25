import Heron.Provider.Refactor
import Heron.AssertEdits
import Heron.AssertNoSuggests
import Lean.Meta.Tactic.Delta
import Lean.PrettyPrinter
import Lean.Server.CodeActions.Basic

open Lean Elab Command Meta Heron.Provider

/-- Run `MetaM` inside a `ContextInfo` context. -/
private def runInfoMetaM (ci : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
  match ← (ci.runMetaM lctx x).toBaseIO with
  | .ok a =>
    return a
  | .error e =>
    throwError "{e}"

/-- Check if an expression references its own name (recursive). -/
private def isRecursive (value : Expr) (name : Name) : Bool :=
  value.find? (fun e => e.isConst && e.constName? == some name) |>.isSome

/-- Find the `declId` node in a command syntax tree. -/
private partial def findDeclId? : Syntax → Option Syntax
  | stx@(.node _ kind args) =>
    if kind == ``Lean.Parser.Command.declId then some stx
    else args.findSome? findDeclId?
  | _ => none

/-- Get the source range of the `declId` in a command, if any. -/
private def getDeclIdRange? (stx : Syntax) : Option Syntax.Range :=
  (findDeclId? stx).bind (·.getRange?)

/-- Check whether a `TermInfo` lies outside the declaration-id range. -/
private def outsideDeclId (declRange? : Option Syntax.Range) (ti : TermInfo) : Bool :=
  match declRange?, ti.stx.getPos? with
  | some r, some p => !r.contains p
  | _, _ => true

/-- Pretty-print an expression inside a `ContextInfo`, returning a parenthesised string. -/
private def ppExprFix? (ci : ContextInfo) (lctx : LocalContext) (e : Expr)
    : CommandElabM (Option String) := do
  try
    let fmt ← runInfoMetaM ci lctx (ppExpr e)
    return some s!"({fmt})"
  catch _ => return none

private structure InlineFixData where
  stx : Syntax
  newText : String

private def isInlineableUsage (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some name =>
    !env.isProjectionFn name && !Meta.isInstanceCore env name &&
      match env.find? name >>= (·.value?) with
      | some v => !isRecursive v name
      | none => false
  | none => false

private def detectInlineOpportunities (stx : Syntax) : CommandElabM (Array InlineFixData) := do
  let trees ← collectElabInfoTrees stx
  let env ← getEnv
  let infos := trees.flatMap collectTermInfos
  let declRange? := getDeclIdRange? stx
  let mut fixes : Array InlineFixData := #[]
  let constCandidates := infos.filter fun (_, ti) => outsideDeclId declRange? ti && isInlineableUsage env ti.expr
  for (ci, ti) in deduplicateTermInfos constCandidates do
    if let some expanded← runInfoMetaM ci ti.lctx (delta? ti.expr) then
      if let some text← ppExprFix? ci ti.lctx expanded then
        fixes := fixes.push { stx := ti.stx, newText := text }
  for (ci, ti) in infos do
    if let .letE _ _ value body _ := ti.expr then
      if let some text← ppExprFix? ci ti.lctx (body.instantiate1 value) then
        fixes := fixes.push { stx := ti.stx, newText := text }
  return fixes

open Server RequestM Lsp in
private def inlineCodeActions : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let startPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  let env := snap.env
  let termInfos := (collectTermInfos snap.infoTree).filter fun (_, ti) =>
    match ti.stx.getPos? true, ti.stx.getTailPos? true with
    | some head, some tail => head ≤ endPos && startPos ≤ tail
    | _, _ => false
  let declRange? := getDeclIdRange? snap.stx
  let constCandidates := termInfos.filter fun (_, ti) =>
    outsideDeclId declRange? ti && isInlineableUsage env ti.expr
  let mut actions : Array LazyCodeAction := #[]
  for (ctx, ti) in deduplicateTermInfos constCandidates do
    let name := ti.expr.getAppFn.constName?.getD `unknown
    actions := actions.push {
      eager := {
        title := s!"Inline '{name}'"
        kind? := "refactor.inline"
      }
      lazy? := some do
        let some expanded ← ctx.runMetaM ti.lctx (delta? ti.expr)
          | return { title := s!"Inline '{name}'", kind? := "refactor.inline" }
        let fmt ← ctx.runMetaM ti.lctx (ppExpr expanded)
        let newText := s!"({fmt})"
        let some range := ti.stx.getRange?
          | return { title := s!"Inline '{name}'", kind? := "refactor.inline" }
        let lspRange := text.utf8RangeToLspRange range
        return {
          title := s!"Inline '{name}'"
          kind? := "refactor.inline"
          edit? := some <| .ofTextEdit doc.versionedIdentifier { range := lspRange, newText }
        }
    }
  for (ctx, ti) in termInfos do
    if let .letE _ _ value body _ := ti.expr then
      actions := actions.push {
        eager := {
          title := "Inline let binding"
          kind? := "refactor.inline"
        }
        lazy? := some do
          let fmt ← ctx.runMetaM ti.lctx (ppExpr (body.instantiate1 value))
          let newText := s!"({fmt})"
          let some range := ti.stx.getRange?
            | return { title := "Inline let binding", kind? := "refactor.inline" }
          let lspRange := text.utf8RangeToLspRange range
          return {
            title := "Inline let binding"
            kind? := "refactor.inline"
            edit? := some <| .ofTextEdit doc.versionedIdentifier { range := lspRange, newText }
          }
      }
  return actions

@[refactor_rule] instance : Refactor InlineFixData where
  ruleName := `inline
  detect := detectInlineOpportunities
  sourceNode := (·.stx)
  hintMessage := m!"Can be inlined."
  replacementText := (·.newText)
  replacementNode := (·.stx)
  codeActions := inlineCodeActions

namespace Tests

def double (n : Nat) :=
  n + n

#assertEdits inline `(term| double 3) => `(term| (3 + 3)) in
example : Nat := double 3

def myConst :=
  42

-- The definition site of `d` should not flag `d` itself for inlining.
#assertNoSuggests inline in
  def d :=
    0

#assertEdits inline `(term| myConst) => `(term| (42)) in
example : Nat := myConst

end Tests
