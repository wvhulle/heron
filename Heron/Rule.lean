import Lean.Elab.Command
import Lean.Server.InfoUtils
import Lean.Compiler.InitAttr
import Heron.Summary

open Lean Elab Command Meta

/-- Recursively collect results from a syntax tree.
`f` is applied at each node; its results are concatenated
with results from all children. -/
partial def Lean.Syntax.collectAll (f : Syntax → Array α) (stx : Syntax) : Array α :=
  f stx ++ stx.getArgs.flatMap (Syntax.collectAll f)

namespace Heron

/-- The text to insert for a replacement: either extracted from a syntax node's
source range, or a literal string for computed replacements. -/
inductive InsertText where
  /-- Extract source text from this syntax node's range in the file. -/
  | ofSyntax (stx : Syntax)
  /-- Use this literal string. -/
  | ofString (s : String)

/-- Resolve the insert text against a file map. -/
def InsertText.resolve (t : InsertText) (fileMap : FileMap) : Option String :=
  match t with
  | .ofSyntax stx => do
    let range ← stx.getRange?
    return String.Pos.Raw.extract fileMap.source range.start range.stop
  | .ofString s => some s

instance : Coe String InsertText := ⟨.ofString⟩
instance : Coe Syntax InsertText := ⟨.ofSyntax⟩

/-- Reprint a syntax node with trailing trivia stripped, then trim whitespace. -/
def reprintTrimmed (stx : Syntax) : String :=
  (stx.updateTrailing "".toRawSubstring |>.reprint.getD "").trimAscii.toString

/-- Extract doElem array from a doSeq node (doSeqIndent or doSeqBracketed). -/
def getDoElems (doSeq : Syntax) : Array Syntax :=
  if doSeq.getKind == ``Parser.Term.doSeqBracketed then
    doSeq[1]!.getArgs.map (·[0]!)
  else if doSeq.getKind == ``Parser.Term.doSeqIndent then
    doSeq[0]!.getArgs.map (·[0]!)
  else
    #[]

/-- A single text replacement with associated source annotation. -/
structure Replacement where
  /-- Syntax node to underline in the diagnostic or anchor the code action. -/
  sourceNode : Syntax
  /-- Syntax node whose range is replaced. -/
  targetNode : Syntax
  /-- Text to insert in place of `targetNode`. -/
  insertText : InsertText
  /-- Inline label shown below the span in editors. -/
  sourceLabel : MessageData

/-- Convert a single replacement to an LSP `TextEdit`. -/
def Replacement.toTextEdit? (r : Replacement) (fileMap : FileMap) : Option Lsp.TextEdit := do
  let range ← r.targetNode.getRange?
  let text ← r.insertText.resolve fileMap
  return { range := fileMap.utf8RangeToLspRange range, newText := text }

class Rule (α : Type) where
  /-- Rule name, used to derive the linter option `linter.<name>`. -/
  ruleName : Name
  /-- Pure detection — set this for rules that don't need `CommandElabM`. -/
  pureDetect : Syntax → Array α := fun _ => #[]
  /-- Detect matches, returning typed match data. Defaults to wrapping `pureDetect`. -/
  detect : Syntax → CommandElabM (Array α) := fun stx => pure (pureDetect stx)
  /-- Message shown as the diagnostic message and suggestion widget hint. -/
  message : α → MessageData
  /-- Per-edit replacement data. -/
  replacements : α → Array Replacement

/-- Master option that enables all Heron linter rules at once. -/
def heronAllOption : Lean.Option Bool :=
  { name := `linter.heron, defValue := false }

initialize
  Lean.registerOption `linter.heron {
    defValue := .ofBool false
    descr := "Enable all Heron linter rules."
    name := `linter
  }

def Rule.option [Rule α] : Lean.Option Bool :=
  { name := `linter ++ Rule.ruleName (α := α), defValue := false }

/-- Check whether this rule is enabled, either individually or via `linter.heron`.
An explicit `set_option linter.<rule> false` overrides `linter.heron true`. -/
def Rule.isEnabled [Rule α] (opts : Options) : Bool :=
  let ruleOpt := `linter ++ Rule.ruleName (α := α)
  if opts.contains ruleOpt then
    (Rule.option (α := α)).get opts
  else
    heronAllOption.get opts

def Rule.initOption [Rule α] : IO Unit :=
  Lean.registerOption (`linter ++ Rule.ruleName (α := α))
    { defValue := .ofBool false
      descr := s! "Enable the {Rule.ruleName (α := α)} linter rule."
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

initialize
  registerTraceClass `heron (inherited := true)

/-- Accumulated per-rule profiling data. -/
structure RuleProfile where
  detectNs : Nat := 0
  fixNs : Nat := 0
  matchCount : Nat := 0
  callCount : Nat := 0

/-- Option to enable per-rule profiling accumulation (without trace output). -/
private def heronProfileOption : Lean.Option Bool :=
  { name := `heron.profile, defValue := false }

initialize
  Lean.registerOption `heron.profile {
    defValue := .ofBool false
    descr := "Accumulate per-rule profiling data for #heronProfile."
    name := `heron
  }

/-- Global accumulator for per-rule timing, gated behind `heron.profile`. -/
initialize heronProfileRef : IO.Ref (Std.HashMap Name RuleProfile) ← IO.mkRef {}

/-- Check whether the `heron.reelaborating` flag is set in the current options. -/
def isReelaborating (opts : Options) : Bool :=
  heronReelaborating.get opts

/-- Run a rule if enabled and not re-elaborating, calling `handle`
for each detected match. -/
def Rule.runIfEnabled [Rule α] (stx : Syntax)
    (handle : α → CommandElabM Unit) : CommandElabM Unit := do
  unless Rule.isEnabled (α := α) (← getOptions) do return
  if isReelaborating (← getOptions) then return
  let name := Rule.ruleName (α := α)
  let profiling := heronProfileOption.get (← getOptions)
  let t0 ← IO.monoNanosNow
  let results ← Rule.detect (α := α) stx
  let t1 ← IO.monoNanosNow
  for m in results do
    handle m
  let t2 ← IO.monoNanosNow
  if profiling then
    let map ← show IO _ from ST.Ref.get heronProfileRef
    let prev := Std.HashMap.getD map name {}
    let map := Std.HashMap.insert map name { prev with
      detectNs := prev.detectNs + (t1 - t0)
      fixNs := prev.fixNs + (t2 - t1)
      matchCount := prev.matchCount + results.size
      callCount := prev.callCount + 1 }
    show IO Unit from ST.Ref.set heronProfileRef map

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
  pure trees

/-- Get existing info trees when available (LSP code action requests),
falling back to re-elaboration when empty (e.g. `#assertRefactor` test flow). -/
def collectInfoTrees (stx : Syntax) : CommandElabM (Array InfoTree) := do
  let existing := (← getInfoState).trees
  if existing.isEmpty then
    collectElabInfoTrees stx
  else
    pure existing.toArray

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
  let map := infos.foldl (init := ({} : Std.HashMap Nat (ContextInfo × TermInfo)))
    fun map (ci, ti) =>
      match ti.stx.getPos? true with
      | some pos =>
        let key := pos.byteIdx
        match map[key]? with
        | some (_, old) =>
          if ti.expr.getAppNumArgs > old.expr.getAppNumArgs
          then map.insert key (ci, ti)
          else map
        | none => map.insert key (ci, ti)
      | none => map
  map.fold (init := #[]) fun acc _ v => acc.push v

/-- Run `MetaM` inside a `ContextInfo` context. -/
def runInfoMetaM (ci : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
  match ← (ci.runMetaM lctx x).toBaseIO with
  | .ok a =>
    pure a
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

/-- Type-erased rule runner: given syntax, produces LSP `TextEdit`s via
`Rule.detect` + `Rule.replacements` + `Replacement.toTextEdit?`. -/
abbrev RuleRunner := Syntax → CommandElabM (Array Lsp.TextEdit)

/-- Registry of rule runners, keyed by rule name. Used by test macros to
invoke rules directly without going through the linter/diagnostic path. -/
initialize ruleRunnersRef : IO.Ref (Std.HashMap Name RuleRunner) ← IO.mkRef {}

/-- Register a type-erased runner for a `Rule` instance. -/
def Rule.registerRunner [Rule α] : IO Unit :=
  ruleRunnersRef.modify fun map =>
    map.insert (Rule.ruleName (α := α)) fun stx => do
      let fileMap ← getFileMap
      let results ← Rule.detect (α := α) stx
      pure (results.flatMap fun m =>
        (Rule.replacements (α := α) m).filterMap (·.toTextEdit? fileMap))

/-- Shared logic for `@[check_rule]` and `@[refactor_rule]` attribute handlers.

Builds an `@[init]` aux decl calling `registerConst` (for import-time registration),
then evaluates `immediateFnConsts` immediately so the rule is active in the current file.
`extraSetup` is called last for any additional registration (e.g. code action providers). -/
unsafe def ruleHandlerCore (attrLabel : String)
    (registerConst : Name) (immediateFnConsts : Array Name)
    (extraSetup : Name → Expr → Expr → AttrM Unit := fun _ _ _ => pure ())
    (declName : Name) : AttrM Unit := do
  let env ← getEnv
  let some info := env.find? declName
    | throwError "@[{attrLabel}]: unknown declaration '{declName}'"
  let some αExpr := info.type.getAppArgs[0]?
    | throwError "@[{attrLabel}]: expected type of the form `... α`"
  let inst := mkConst declName
  let auxType := mkApp (mkConst ``IO) (mkConst ``Unit)
  let some regInfo := env.find? registerConst
    | throwError "{registerConst} not found"
  let levels := regInfo.levelParams.map fun _ => Level.zero
  -- Aux decl 1: calls `register` (initOption + registerRunner + addLinter), tagged @[init]
  let registerName := declName ++ `_rule_init
  addAndCompile <| .defnDecl {
    name := registerName, levelParams := [], type := auxType
    value := mkApp2 (mkConst registerConst levels) αExpr inst
    hints := .opaque, safety := .unsafe
  }
  modifyEnv fun env =>
    match regularInitAttr.setParam env registerName .anonymous with
    | .ok env' => env'
    | .error _ => env
  -- Evaluate immediate functions for current file (e.g. addLinter, registerRunner)
  for fnConst in immediateFnConsts do
    let some fnInfo := (← getEnv).find? fnConst
      | throwError "{fnConst} not found"
    let fnLevels := fnInfo.levelParams.map fun _ => Level.zero
    let auxName := declName ++ (`_rule).append fnConst
    addAndCompile <| .defnDecl {
      name := auxName, levelParams := [], type := auxType
      value := mkApp2 (mkConst fnConst fnLevels) αExpr inst
      hints := .opaque, safety := .unsafe
    }
    let fn ← IO.ofExcept <| (← getEnv).evalConst (IO Unit) {} auxName
    fn
  extraSetup declName αExpr inst

syntax (name := heronProfileCmd) "#heronProfile" : command

@[command_elab heronProfileCmd] def elabHeronProfile : CommandElab
  | stx => do
    let map ← show IO _ from ST.Ref.get heronProfileRef
    if map.isEmpty then
      logInfoAt stx "No profiling data collected. Enable with: set_option heron.profile true"
      return
    let entries := Std.HashMap.fold (init := #[]) (fun acc name profile => acc.push (name, profile)) map
    let sorted := entries.qsort fun a b => a.2.detectNs + a.2.fixNs > b.2.detectNs + b.2.fixNs
    let columns : Array Column :=
      #[⟨"Rule", '─'⟩, ⟨"Detect", '─'⟩, ⟨"Fix", '─'⟩,
        ⟨"Total", '─'⟩, ⟨"Matches", '─'⟩, ⟨"Calls", '─'⟩]
    let fmtMs (ns : Nat) : String :=
      let us := (ns + 500) / 1000  -- round to nearest microsecond
      let ms := us / 1000
      let frac := us % 1000
      let fracStr := toString frac
      let padded := String.ofList (List.replicate (3 - fracStr.length) '0') ++ fracStr
      s!"{ms}.{padded}ms"
    let rows := sorted.map fun (name, p) =>
      #[toString name, fmtMs p.detectNs, fmtMs p.fixNs,
        fmtMs (p.detectNs + p.fixNs),
        toString p.matchCount, toString p.callCount]
    logInfoAt stx ("Heron profile:" ++ Format.line ++ renderTable columns rows)
    show IO Unit from ST.Ref.set heronProfileRef {}

end Heron
