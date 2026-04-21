module

public meta import Lean.Elab.Command
public meta import Lean.Server.InfoUtils
public meta import Lean.PrettyPrinter
public meta import Heron.Profiling
public meta import Heron.TestRunner

public section

open Lean Elab Command Meta

/-- Recursively collect results from a syntax tree.
`f` is applied at each node; its results are concatenated
with results from all children. -/
partial def Lean.Syntax.collectAll (f : Syntax → Array α) (stx : Syntax) : Array α :=
  f stx ++ stx.getArgs.flatMap (Syntax.collectAll f)

namespace Heron

/-- Reprint a syntax node with trailing trivia stripped, then trim whitespace. -/
meta def reprintTrimmed (stx : Syntax) : String :=
  (stx.updateTrailing "".toRawSubstring |>.reprint.getD "").trimAscii.toString

/-- Extract doElem array from a doSeq node (doSeqIndent or doSeqBracketed). -/
meta def getDoElems (doSeq : Syntax) : Array Syntax :=
  if doSeq.getKind == ``Parser.Term.doSeqBracketed then doSeq[1]!.getArgs.map (·[0]!)
  else if doSeq.getKind == ``Parser.Term.doSeqIndent then doSeq[0]!.getArgs.map (·[0]!) else #[]

/-- A single text replacement with associated source annotation. -/
structure Replacement where
  /-- Syntax node to underline in the diagnostic or anchor the code action. -/
  emphasizedSyntax : Syntax
  /-- Syntax node whose range is replaced. -/
  oldSyntax : Syntax
  /-- Syntax to insert in place of `targetNode`. -/
  newSyntax : Syntax
  /-- Inline label shown below the span in editors. -/
  inlineViolationLabel : MessageData
  /-- Syntax category for pretty-printing (e.g. `term`, `tactic`, `doElem`). -/
  category : Name := `term

/-- Convert a single replacement to an LSP `TextEdit`, using Lean's pretty printer
to format the replacement text. Falls back to `reprint` if formatting fails. -/
meta def Replacement.toTextEdit (r : Replacement) (fileMap : FileMap) : CoreM (Option Lsp.TextEdit) := do
  let some range := r.oldSyntax.getRange? | return none
  let lspRange := fileMap.utf8RangeToLspRange range
  if r.newSyntax.isMissing then
    return some { range := lspRange, newText := "" }
  let newText ← try
    pure (← PrettyPrinter.ppCategory r.category r.newSyntax).pretty
  catch _ =>
    let some text := r.newSyntax.reprint | return none
    pure text.trimAscii.toString
  return some { range := lspRange, newText }

class Rule (α : Type) where
  /-- Rule name, used to derive the linter option `linter.<name>`. -/
  name : Name
  /-- Pure detection — set this for rules that don't need `CommandElabM`. -/
  find : Syntax → Array α := fun _ => #[]
  /-- Detect matches, returning typed match data. -/
  detect : Syntax → CommandElabM (Array α) := fun stx => pure (find stx)
  /-- Message shown as the diagnostic message and suggestion widget hint. -/
  message : α → MessageData
  /-- Per-edit replacement data. -/
  replacements : α → CommandElabM (Array Replacement)

/-- Master option that enables all Heron linter rules at once. -/
meta def Heron.allRulesLinterOption : Lean.Option Bool :=
  { name := `linter.heron, defValue := false }

meta initialize
  Lean.registerOption `linter.heron
      { defValue := .ofBool false
        descr := "Enable all Heron linter rules."
        name := `linter }

meta def Rule.linterOption [Rule α] : Lean.Option Bool :=
  { name := `linter ++ Rule.name (α := α), defValue := false }

/-- Check whether this rule is enabled, either individually or via `linter.heron`.
An explicit `set_option linter.<rule> false` overrides `linter.heron true`. -/
meta def Rule.isEnabled [Rule α] (opts : Options) : Bool :=
  let ruleOpt := `linter ++ Rule.name (α := α)
  if opts.contains ruleOpt then (Rule.linterOption (α := α)).get opts else Heron.allRulesLinterOption.get opts

meta def Rule.registerLinterOption (ruleName : Name) : IO Unit :=
  Lean.registerOption (`linter ++ ruleName)
    { defValue := .ofBool false
      descr := s!"Enable the {ruleName} linter rule."
      name := `linter }

/-- Internal option to prevent recursive linter invocation during re-elaboration. -/
private meta def Heron.reelaboratingGuardOption : Lean.Option Bool :=
  { name := `heron.reelaborating, defValue := false }

meta initialize
  Lean.registerOption `heron.reelaborating
      { defValue := .ofBool false
        descr := "Internal: set during re-elaboration to prevent recursive linter invocation."
        name := `heron }

meta initialize
  registerTraceClass `heron (inherited := true)

/-- Check whether the `heron.reelaborating` flag is set in the current options. -/
meta def Heron.isReelaboratingGuardSet (opts : Options) : Bool :=
  Heron.reelaboratingGuardOption.get opts

/-- Run a rule if enabled and not re-elaborating, calling `handle`
for each detected match. -/
meta def Rule.runIfEnabled [Rule α] (stx : Syntax) (handle : α → CommandElabM Unit) : CommandElabM Unit := do
  unless Rule.isEnabled (α := α) (← getOptions) do return
  if Heron.isReelaboratingGuardSet (← getOptions) then return
  let name := Rule.name (α := α)
  let profiling := Heron.isProfilingEnabled (← getOptions)
  let t0 ← IO.monoNanosNow
  let results ← Rule.detect (α := α) stx
  let t1 ← IO.monoNanosNow
  for m in results do handle m
  let t2 ← IO.monoNanosNow
  if profiling then
    Heron.recordProfile name (t1 - t0) (t2 - t1) results.size

/-- Re-elaborate a command collecting info trees.

Uses the scoped `heron.reelaborating` option instead of clearing the global
`lintersRef` to prevent recursive linter invocation. This is safe under
concurrent (async) elaboration — `withScope` modifies only the current
command's options, so other commands' linters are unaffected. -/
meta def collectElabInfoTrees (stx : Syntax) : CommandElabM (Array InfoTree) := do
  let savedInfoState ← getInfoState
  let savedMessages := (← get).messages
  setInfoState { enabled := true, trees := { } }
  try
    withoutModifyingEnv do
      withScope
        (fun scope =>
          { scope with opts := Heron.reelaboratingGuardOption.set (Elab.async.set scope.opts false) true })
        do withReader ({ · with snap? := none }) (elabCommand stx)
  catch _ => pure ()
  let trees := (← getInfoState).trees.toArray
  setInfoState savedInfoState
  modify ({ · with messages := savedMessages })
  return trees

/-- Get existing info trees when available (LSP code action requests),
falling back to re-elaboration when empty (e.g. `#assertRefactor` test flow). -/
meta def collectInfoTrees (stx : Syntax) : CommandElabM (Array InfoTree) := do
  let existing := (← getInfoState).trees
  if existing.isEmpty then collectElabInfoTrees stx
  else return existing.toArray

/-- Extract `(ContextInfo × TermInfo)` pairs from an info tree. -/
meta def collectTermInfos (tree : InfoTree) : Array (ContextInfo × TermInfo) :=
  tree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofTermInfo ti => acc.push (ctx, ti)
    | _ => acc

/-- Deduplicate term infos sharing a start position, keeping the most applied.

Lean's elaborator produces multiple `TermInfo` nodes for the same source
position at different application depths (e.g. `f`, `f x`, `f x y`).
This keeps only the most-applied version per position. -/
meta def deduplicateTermInfos (infos : Array (ContextInfo × TermInfo)) : Array (ContextInfo × TermInfo) :=
  let dominated (old new : TermInfo) := new.expr.getAppNumArgs > old.expr.getAppNumArgs
  let map := infos.foldl (init := ({} : Std.HashMap Nat (ContextInfo × TermInfo))) fun map (ci, ti) =>
    match ti.stx.getPos? true with
    | some pos =>
      match map[pos.byteIdx]? with
      | some (_, old) => if dominated old ti then map.insert pos.byteIdx (ci, ti) else map
      | none => map.insert pos.byteIdx (ci, ti)
    | none => map
  map.values.toArray

/-- Run `MetaM` inside a `ContextInfo` context. -/
meta def runInfoMetaM (ci : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
  IO.ofExcept (← (ci.runMetaM lctx x).toBaseIO)

/-- Find the `declId` node in a command syntax tree. -/
meta partial def findDeclId? : Syntax → Option Syntax
  | stx@(.node _ kind args) => if kind == ``Lean.Parser.Command.declId then some stx else args.findSome? findDeclId?
  | _ => none

/-- Get the source range of the `declId` in a command, if any. -/
meta def getDeclIdRange? (stx : Syntax) : Option Syntax.Range := do
  (← findDeclId? stx).getRange?

/-- Check whether a `TermInfo` lies outside the declaration-id range. -/
meta def outsideDeclId (declRange? : Option Syntax.Range) (ti : TermInfo) : Bool :=
  match declRange?, ti.stx.getPos? with
  | some r, some p => !r.contains p
  | _, _ => true

/-- Pretty-print an expression inside a `ContextInfo`, returning a parenthesised string. -/
meta def ppExprFix? (ci : ContextInfo) (lctx : LocalContext) (e : Expr) : CommandElabM (Option String) :=
  try return some s!"({← runInfoMetaM ci lctx (ppExpr e)})"
  catch _ => return none

/-- Build a type-erased test runner for a `Rule` instance. -/
meta def Rule.buildTestRunner [Rule α] : Rule.TestRunner := fun stx => do
  let fileMap ← getFileMap
  let results ← Rule.detect (α := α) stx
  results.flatMapM fun m => do
    let repls ← Rule.replacements (α := α) m
    repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)

end Heron
