import Heron.Rules.Basic
import Lean.Meta.Tactic.Delta
import Lean.PrettyPrinter

open Lean Elab Command Meta Heron.Rules

/-- Extract `(ContextInfo × TermInfo)` pairs from an info tree. -/
private def collectTermInfos (tree : InfoTree) : Array (ContextInfo × TermInfo) :=
  tree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofTermInfo ti => acc.push (ctx, ti)
    | _ => acc

/-- Run `MetaM` inside a `ContextInfo` context. -/
private def runInfoMetaM (ci : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
  match ← (ci.runMetaM lctx x).toBaseIO with
  | .ok a =>
    return a
  | .error e =>
    throwError "{e}"

/-- Deduplicate term infos sharing a start position, keeping the most applied. -/
private def deduplicateByPosition (usages : Array (ContextInfo × TermInfo)) : Array (ContextInfo × TermInfo) :=
  usages.foldl (init := #[]) fun acc (ci, ti) =>
    match ti.stx.getPos? true with
    | some pos =>
      let dominated :=
        acc.any fun (_, old) => old.stx.getPos? true == some pos && old.expr.getAppNumArgs >= ti.expr.getAppNumArgs
      if dominated then acc
      else
        let acc :=
          acc.filter fun (_, old) =>
            !(old.stx.getPos? true == some pos && old.expr.getAppNumArgs < ti.expr.getAppNumArgs)
        acc.push (ci, ti)
    | none => acc

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
  let trees ← Heron.collectElabInfoTrees stx
  let env ← getEnv
  let infos := trees.flatMap collectTermInfos
  let declRange? := getDeclIdRange? stx
  let mut fixes : Array InlineFixData := #[]
  let constCandidates := infos.filter fun (_, ti) => outsideDeclId declRange? ti && isInlineableUsage env ti.expr
  for (ci, ti) in deduplicateByPosition constCandidates do
    if let some expanded← runInfoMetaM ci ti.lctx (delta? ti.expr) then
      if let some text← ppExprFix? ci ti.lctx expanded then
        fixes := fixes.push { stx := ti.stx, newText := text }
  for (ci, ti) in infos do
    if let .letE _ _ value body _ := ti.expr then
      if let some text← ppExprFix? ci ti.lctx (body.instantiate1 value) then
        fixes := fixes.push { stx := ti.stx, newText := text }
  return fixes

instance : Rule InlineFixData where
  ruleName := `inline
  severity := .warning
  detect := detectInlineOpportunities
  diagnosticNode := (·.stx)
  hintMessage := m!"Can be inlined."
  diagnosticMessage := m!"Inline."
  replacementText := (·.newText)
  replacementNode := (·.stx)
  diagnosticTags := #[]

initialize
  Rule.initOption (α := InlineFixData)
initialize
  Rule.addLinter (α := InlineFixData)

namespace Tests

#eval Rule.addLinter (α := InlineFixData)

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
