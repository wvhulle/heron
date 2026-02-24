import Heron.Rules.Basic
import Lean.Meta.Tactic.Delta
import Lean.PrettyPrinter

open Lean Elab Command Meta Heron.Rules

private structure InlineFixData where
  stx : Syntax
  newText : String

/-- Find the `declId` node in a command syntax tree. -/
private partial def findDeclId? : Syntax → Option Syntax
  | stx@(.node _ kind args) =>
    if kind == ``Lean.Parser.Command.declId then some stx
    else args.findSome? findDeclId?
  | _ => none

/-- Get the source range of the `declId` in a command, if any. -/
private def getDeclIdRange? (stx : Syntax) : Option Syntax.Range :=
  (findDeclId? stx).bind (·.getRange?)

private def isInlineableUsage (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some name =>
    !env.isProjectionFn name &&
    !Meta.isInstanceCore env name &&
    match env.find? name >>= (·.value?) with
    | some v => !isRecursive v name
    | none => false
  | none => false

private def outsideDeclId (declRange? : Option Syntax.Range) (ti : TermInfo) : Bool :=
  match declRange?, ti.stx.getPos? with
  | some r, some p => !r.contains p
  | _, _ => true

private def tryPpFix (ci : ContextInfo) (ti : TermInfo) (expanded : Expr)
    : CommandElabM (Option InlineFixData) := do
  try
    let fmt ← runInfoMetaM ci ti.lctx (ppExpr expanded)
    return some { stx := ti.stx, newText := s!"({fmt})" }
  catch _ => return none

private def detectInlineOpportunities (stx : Syntax) : CommandElabM (Array InlineFixData) := do
  let trees ← collectElabInfoTrees stx
  let env ← getEnv
  let infos := trees.flatMap collectTermInfos
  let declRange? := getDeclIdRange? stx
  let mut fixes : Array InlineFixData := #[]
  let constCandidates := infos.filter fun (_, ti) =>
    outsideDeclId declRange? ti && isInlineableUsage env ti.expr
  for (ci, ti) in deduplicateByPosition constCandidates do
    if let some expanded ← runInfoMetaM ci ti.lctx (delta? ti.expr) then
      if let some fix ← tryPpFix ci ti expanded then
        fixes := fixes.push fix
  for (ci, ti) in infos do
    if let .letE _ _ value body _ := ti.expr then
      if let some fix ← tryPpFix ci ti (body.instantiate1 value) then
        fixes := fixes.push fix
  return fixes

instance : Rule InlineFixData where
  name := `inline
  severity := .warning
  detect := detectInlineOpportunities
  diagStx := (·.stx)
  hintMsg := m!"Can be inlined."
  diagMsg := m!"Inline."
  toSuggestion := fun d => { suggestion := d.newText, span? := some d.stx }

initialize Rule.initOption (α := InlineFixData)
initialize Rule.addLinter (α := InlineFixData)

namespace Tests

#eval Rule.addLinter (α := InlineFixData)

def double (n : Nat) := n + n

#assertEdits inline `(term| double 3) => `(term| (3 + 3)) in
example : Nat := double 3

def myConst := 42

-- The definition site of `d` should not flag `d` itself for inlining.
#assertNoSuggests inline in
def d := 0

#assertEdits inline `(term| myConst) => `(term| (42)) in
example : Nat := myConst

end Tests
