module

public meta import Lean.Elab.Command
public meta import Lean.Elab.BuiltinCommand
public meta import Lean.Server.InfoUtils
public meta import Lean.PrettyPrinter
public meta import Heron.Source

public section

open Lean Elab Command Meta

namespace Heron

/-- A range-anchored label surfaced via LSP `Diagnostic.relatedInformation`. -/
structure Label where
  /-- Source node whose range the label points at. -/
  span : Syntax
  /-- Label text shown next to the span by clients that render `relatedInformation`. -/
  text : MessageData

/-- A single text replacement with associated source annotation.

A replacement carries both an edit (`oldSyntax → newSyntax`) and the label
metadata (`emphasizedSyntax`, `inlineViolationLabel`) used to render that edit
as a `relatedInformation` entry on the published diagnostic. The two roles are
kept on one record because every replacement currently produces both; rules
that need a label *without* an edit use `Rule.labels` instead. -/
structure Replacement where
  /-- Source range used to anchor both the LSP `relatedInformation` label and
  the code action attached to this edit. -/
  emphasizedSyntax : Syntax
  /-- Syntax node whose range is replaced. -/
  oldSyntax : Syntax
  /-- Syntax to insert in place of `oldSyntax`. -/
  newSyntax : Syntax
  /-- Label surfaced via LSP `relatedInformation`, anchored at `emphasizedSyntax`. -/
  inlineViolationLabel : MessageData
  prettyPrint : Syntax → CoreM Format := PrettyPrinter.ppCategory `term

/-- Promote a replacement's label metadata to a standalone `Label` for
relatedInformation emission. -/
meta def Replacement.toLabel (r : Replacement) : Label :=
  { span := r.emphasizedSyntax, text := r.inlineViolationLabel }

/-- Core rule typeclass. The harness walks each command syntax tree once and
calls `detect` only at nodes whose kind is in `kinds`. Both `kinds` and `detect`
are required: missing either is a compile-time error, ruling out silent no-ops. -/
class Rule (α : Type) where
  /-- Rule name, used to derive the linter option `linter.<name>`. -/
  name : Name
  description : String
  /-- Syntax kinds at which this rule fires. The harness only invokes `detect`
  on nodes whose `getKind` is in this array. -/
  kinds : Array SyntaxNodeKind
  /-- Per-node detector. Receives a node whose kind is one of `kinds`; returns
  matches that originate at this node. -/
  detect : Syntax → CommandElabM (Array α)
  /-- Message shown as the diagnostic message and suggestion widget hint. -/
  message : α → MessageData
  /-- Per-edit replacement data, or `none` for a rule that only flags code. Each replacement
  also produces a `relatedInformation` entry via `Replacement.toLabel`. -/
  replacements : Option (α → CommandElabM (Array Replacement)) := none
  /-- Extra `relatedInformation` labels not tied to any replacement. Use this
  for label-only annotations — e.g. pointing at a related declaration that
  caused the diagnostic but is not itself being edited. Defaults to empty. -/
  labels : α → CommandElabM (Array Label) := fun _ => pure #[]
  /-- When `true`, the walker stops descending into a node's children whenever
  `detect` produces matches at that node. Use this for rules that emit at every
  level of a nested chain and want only the outermost match (e.g. `Expr.app`
  chains, `>>=` chains). -/
  consumesSubtree : Bool := false
  within : Array SyntaxNodeKind := #[]
  sources : Array Source := #[]

inductive RuleKind where
  | check
  | refactor
  deriving Inhabited, BEq

structure RuleSummary where
  name : Name
  kind : RuleKind
  description : String
  sources : Array Source
  offersFix : Bool

meta initialize ruleCatalog : IO.Ref (Array RuleSummary) ← IO.mkRef #[]

meta def Rule.replacementsFor [Rule α] (m : α) : CommandElabM (Array Replacement) :=
  match Rule.replacements (α := α) with
  | some replacements => replacements m
  | none => pure #[]

meta def Rule.offersFix [Rule α] : Bool := (Rule.replacements (α := α)).isSome

/-- Master option that enables all Heron linter rules at once. -/
private meta def Heron.allRulesLinterOption : Lean.Option Bool :=
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

meta def registerLinterOption (ruleName : Name) : IO Unit := do
  let optionName := `linter ++ ruleName
  unless (← getOptionDecls).contains optionName do
    Lean.registerOption optionName
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

structure SyntaxVisitor where
  kinds : Array SyntaxNodeKind
  within : Array SyntaxNodeKind
  visit : Syntax → CommandElabM Unit

meta def walkedChildren : Syntax → Array Syntax
  | .node _ kind args => if kind == choiceKind then args.extract 0 1 else args
  | _ => #[]

private meta partial def walkWithVisitorTable (table : Std.HashMap SyntaxNodeKind (Array SyntaxVisitor))
    (enclosingKinds : Array SyntaxNodeKind) (stx : Syntax) : CommandElabM Unit := do
  let enclosingKinds := enclosingKinds.push stx.getKind
  if let some visitors := table[stx.getKind]? then
    for visitor in visitors do
      if visitor.within.isEmpty || enclosingKinds.any visitor.within.contains then visitor.visit stx
  for child in walkedChildren stx do walkWithVisitorTable table enclosingKinds child

private meta def nodeKindsNamedBy (categories : Parser.ParserCategories) (kind : SyntaxNodeKind) :
    Array SyntaxNodeKind :=
  match categories.find? kind with
  | some category => category.kinds.foldl (init := #[]) fun kinds categoryKind _ => kinds.push categoryKind
  | none => #[kind]

meta def walkVisitors (visitors : Array SyntaxVisitor) (stx : Syntax) : CommandElabM Unit := do
  let categories := (Parser.parserExtension.getState (← getEnv)).categories
  let table := visitors.foldl (init := {}) fun table visitor =>
    (visitor.kinds.flatMap (nodeKindsNamedBy categories)).foldl (init := table) fun table kind =>
      table.insert kind ((table[kind]?.getD #[]).push visitor)
  walkWithVisitorTable table #[] stx

meta def Rule.collectingVisitor [Rule α] (found : IO.Ref (Array α)) : CommandElabM SyntaxVisitor := do
  let consumedRanges ← IO.mkRef (#[] : Array Syntax.Range)
  let consumes := Rule.consumesSubtree (α := α)
  return {
    kinds := Rule.kinds (α := α)
    within := Rule.within (α := α)
    visit := fun node => do
      if consumes then
        if let some r := node.getRange? then
          if (← consumedRanges.get).any fun c => c.start ≤ r.start ∧ r.stop ≤ c.stop then return
      let detected ← Rule.detect (α := α) node
      if detected.isEmpty then return
      found.modify (· ++ detected)
      if consumes then
        if let some r := node.getRange? then consumedRanges.modify (·.push r) }

meta def Rule.detectAll [Rule α] (stx : Syntax) : CommandElabM (Array α) := do
  let found ← IO.mkRef #[]
  walkVisitors #[← Rule.collectingVisitor found] stx
  found.get

/-- Re-elaborate a command collecting info trees.

Uses the scoped `heron.reelaborating` option instead of clearing the global
`lintersRef` to prevent recursive linter invocation. This is safe under
concurrent (async) elaboration — `withScope` modifies only the current
command's options, so other commands' linters are unaffected. -/
private meta def reelaborateIsolated (stx : Syntax) (namespaceName : Name := .anonymous) :
    CommandElabM (Array InfoTree × Bool) := do
  let savedInfoState ← getInfoState
  let savedMessages := (← get).messages
  setInfoState { enabled := true, trees := { } }
  modify ({ · with messages := {} })
  let threw ← try
    withoutModifyingEnv do
      withScope
        (fun scope =>
          { scope with opts := Heron.reelaboratingGuardOption.set (Elab.async.set scope.opts false) true })
        do withReader ({ · with snap? := none }) do
          if namespaceName.isAnonymous then elabCommand stx
          else withNamespace namespaceName (elabCommand stx)
    pure false
  catch _ => pure true
  let trees := (← getInfoState).trees.toArray
  let succeeded := !threw && !(← get).messages.hasErrors
  setInfoState savedInfoState
  modify ({ · with messages := savedMessages })
  return (trees, succeeded)

private meta def collectElabInfoTrees (stx : Syntax) : CommandElabM (Array InfoTree) :=
  Prod.fst <$> reelaborateIsolated stx

meta def elaboratesWithoutErrorsInProbeNamespace (stx : Syntax) : CommandElabM Bool :=
  Prod.snd <$> reelaborateIsolated stx `Heron.Probe

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

/-- Resolve `stx` to its elaborated `Expr` and run `f` in that `MetaM`
context. Returns `none` if no `TermInfo` is found at `stx`'s start position.
The most-applied `TermInfo` per position wins (see `deduplicateTermInfos`). -/
meta def runMetaMForSyntax (stx : Syntax) (f : Expr → MetaM α) :
    CommandElabM (Option α) := do
  let some pos := stx.getPos? true | return none
  let trees ← collectInfoTrees stx
  let deduped := deduplicateTermInfos (trees.flatMap collectTermInfos)
  let some (ci, ti) := deduped.find? fun (_, ti) =>
    ti.stx.getPos? true |>.any (·.byteIdx == pos.byteIdx) | return none
  some <$> runInfoMetaM ci ti.lctx (f ti.expr)

meta def runMetaMForEachExactTermInfo (stx : Syntax) (f : TermInfo → MetaM α) :
    CommandElabM (Array α) := do
  let some range := stx.getRange? | return #[]
  let trees ← collectInfoTrees stx
  let exactMatches := (trees.flatMap collectTermInfos).filter fun (_, ti) =>
    ti.stx.getRange?.any fun r => r.start == range.start && r.stop == range.stop
  exactMatches.mapM fun (ci, ti) => runInfoMetaM ci ti.lctx (f ti)

meta def runMetaMForEachExactSyntax (stx : Syntax) (f : Expr → MetaM α) :
    CommandElabM (Array α) :=
  runMetaMForEachExactTermInfo stx (f ·.expr)

meta def elaboratesToApplicationOf (stx : Syntax) (constName : Name) : CommandElabM Bool := do
  let applications ← runMetaMForEachExactSyntax stx fun e =>
    return (← instantiateMVars e).getAppFn.isConstOf constName
  return applications.any id

private meta def sameRange (a b : Syntax) : Bool :=
  match a.getRange?, b.getRange? with
  | some ra, some rb => ra.start == rb.start && ra.stop == rb.stop
  | _, _ => false

meta def liesWithin (scope inner : Syntax) : Bool :=
  match scope.getRange?, inner.getRange? with
  | some outer, some r => outer.start ≤ r.start && r.stop ≤ outer.stop
  | _, _ => false

meta def declaredConstant? (declId : Syntax) (infos : Array (ContextInfo × TermInfo)) : Option Name :=
  infos.findSome? fun (_, ti) => if ti.isBinder && liesWithin declId ti.stx then ti.expr.constName? else none

meta def bindsVariables (scope : Syntax) : CommandElabM Bool := do
  let infos := (← collectInfoTrees scope).flatMap collectTermInfos
  return infos.any fun (_, ti) => ti.isBinder && liesWithin scope ti.stx

meta def boundVariableReferences (binder scope : Syntax) : CommandElabM (Array Syntax) := do
  let infos := (← collectInfoTrees scope).flatMap collectTermInfos
  let some (_, binderInfo) := infos.find? fun (_, ti) => ti.isBinder && sameRange ti.stx binder
    | return #[]
  let .fvar fvarId := binderInfo.expr | return #[]
  let references := infos.filter fun (_, ti) =>
    !ti.isBinder && ti.expr == .fvar fvarId && liesWithin scope ti.stx
  return (deduplicateTermInfos references).map (·.2.stx)

private meta def runTermElabAtTermInfo (ci : ContextInfo) (ti : TermInfo) (x : TermElabM α) : CommandElabM α := do
  let fileMap ← getFileMap
  let fileName ← getFileName
  runInfoMetaM ci ti.lctx do
    withTheReader Core.Context (fun ctx => { ctx with fileMap, fileName }) do
    Meta.withLocalInstances (ti.lctx.decls.toList.filterMap id) do
      x.run'

private meta def elaboratesToExpected (candidate : Syntax) (expectedType? : Option Expr) (expected : Expr) :
    TermElabM Bool := do
  try
    Term.withoutErrToSorry do
      let elaborated ← Term.elabTermEnsuringType candidate expectedType?
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.withReducible <| Meta.isDefEq (← instantiateMVars elaborated) (← instantiateMVars expected)
  catch _ => return false

meta def elaboratesLike (original : Syntax) (candidate : Term) : CommandElabM Bool := do
  let infos := (← collectInfoTrees original).flatMap collectTermInfos
  let some (ci, ti) := infos.find? fun (_, ti) => sameRange ti.stx original | return false
  try
    runTermElabAtTermInfo ci ti <| withRef original <| elaboratesToExpected candidate ti.expectedType? ti.expr
  catch _ => return false

private meta def outermostSourceOf (candidates : Array (ContextInfo × TermInfo)) (assigned : Expr) :
    MetaM (Option Syntax) := do
  let mut outermost : Option Syntax := none
  for (_, ti) in candidates do
    unless (← instantiateMVars ti.expr) == assigned do continue
    let wider := match outermost with
      | some current => liesWithin ti.stx current
      | none => true
    if wider then outermost := some ti.stx
  return outermost

private meta def equationVariableName (index : Nat) : Name := .mkSimple s!"heronEquationVariable{index}"

private meta partial def withEquationVariables (statement : Expr) (variables : Array Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α :=
  match statement with
  | .forallE _ domain body binderInfo =>
    withLocalDecl (equationVariableName variables.size) binderInfo domain fun boundVariable =>
      withEquationVariables (body.instantiate1 boundVariable) (variables.push boundVariable) k
  | body => k variables body

private meta def matchedAndPrintedSides (statement : Expr) (rightToLeft : Bool) : Option (Expr × Expr) := do
  let (_, lhs, rhs) ← statement.eq?
  return if rightToLeft then (rhs, lhs) else (lhs, rhs)

private meta def dischargeHypotheses (variables : Array Expr) (binderInfos : Array BinderInfo) : MetaM Bool := do
  for (hypothesis, binderInfo) in variables.zip binderInfos do
    let hypothesis ← instantiateMVars hypothesis
    unless hypothesis.isMVar do continue
    let type ← instantiateMVars (← inferType hypothesis)
    if binderInfo.isInstImplicit then
      let some synthesized ← synthInstance? type | return false
      unless ← isDefEq hypothesis synthesized do return false
    else if ← isProp type then return false
  return true

private structure EquationSideMatch where
  pieces : Array Syntax
  expected : Expr

private meta def matchEquationSide (equation : Name) (rightToLeft : Bool)
    (candidates : Array (ContextInfo × TermInfo)) (target : Expr) : MetaM (Option EquationSideMatch) := do
  let (variables, binderInfos, statement) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels equation))
  let some (matched, printed) := matchedAndPrintedSides statement rightToLeft | return none
  unless ← withTransparency .instances <| isDefEq matched (← instantiateMVars target) do return none
  unless ← dischargeHypotheses variables binderInfos do return none
  let pieces ← variables.mapM fun patternVariable => do
    let assigned ← instantiateMVars patternVariable
    match ← outermostSourceOf candidates assigned with
    | some piece => return piece
    | none => return (← PrettyPrinter.delab assigned).raw
  return some { pieces, expected := ← instantiateMVars printed }

private meta partial def identifierNamesIn (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId] else stx.getArgs.flatMap identifierNamesIn

private meta def freshNameAvoiding (taken : Array Name) (name : Name) : Name := Id.run do
  unless taken.contains name do return name
  let mut index := 1
  while taken.contains (name.appendIndexAfter index) do index := index + 1
  return name.appendIndexAfter index

private meta partial def renameBindersAvoiding (taken : Array Name) : Expr → Expr
  | .lam name type body info =>
    .lam (freshNameAvoiding taken name) (renameBindersAvoiding taken type) (renameBindersAvoiding taken body) info
  | .forallE name type body info =>
    .forallE (freshNameAvoiding taken name) (renameBindersAvoiding taken type) (renameBindersAvoiding taken body) info
  | .app function argument => .app (renameBindersAvoiding taken function) (renameBindersAvoiding taken argument)
  | .mdata data inner => .mdata data (renameBindersAvoiding taken inner)
  | other => other

private meta def delaboratedEquationSide (equation : Name) (rightToLeft : Bool) (pieces : Array Syntax) :
    MetaM (Option Syntax) := do
  let taken := pieces.flatMap identifierNamesIn
  withEquationVariables (← inferType (← mkConstWithFreshMVarLevels equation)) #[] fun _ statement => do
    let some (_, printed) := matchedAndPrintedSides statement rightToLeft | return none
    return some (← PrettyPrinter.delab (renameBindersAvoiding taken printed)).raw

private meta def withoutParentheses : Syntax → Syntax
  | `(($inner)) => inner
  | piece => piece

private meta def spliceSourcePieces (rhs : Syntax) (pieces : Array Syntax) : Option Syntax :=
  rhs.replaceM fun stx => do
    let some index := (List.range pieces.size).find? fun index => stx.isIdent && stx.getId == equationVariableName index
      | return none
    return some (withoutParentheses (← pieces[index]?))

private meta def equationSideHead? (equation : Name) (rightToLeft : Bool) : MetaM (Option Name) := do
  let (_, _, statement) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels equation))
  let some (matched, _) := matchedAndPrintedSides statement rightToLeft | return none
  return matched.getAppFn.constName?

private meta def headsLike (head : Name) (target : Expr) : MetaM Bool := do
  if target.getAppFn.isConstOf head then return true
  let some unfolded ← unfoldProjInst? target | return false
  return unfolded.getAppFn.isConstOf head

private meta def sourceNodeAt (command piece : Syntax) : Syntax := Id.run do
  let some range := piece.getRange? | return piece
  return (command.find? fun node =>
    !node.isOfKind nullKind && node.getRange? (canonicalOnly := true) == some range).getD piece

private meta def oneInfoPerRange (infos : Array (ContextInfo × TermInfo)) : Array (ContextInfo × TermInfo) :=
  infos.foldl (init := #[]) fun kept (ci, ti) =>
    if kept.any fun (_, seen) => sameRange seen.stx ti.stx then kept else kept.push (ci, ti)

private meta def rangeSize (stx : Syntax) : Nat :=
  (stx.getRange?.map fun range => range.stop.byteIdx - range.start.byteIdx).getD 0

meta def rewritesByEquationIn (command : Syntax) (equation : Name) (rightToLeft : Bool) :
    CommandElabM (Array (Syntax × Syntax)) := do
  let infos := (← collectInfoTrees command).flatMap collectTermInfos |>.filter fun (_, ti) =>
    !ti.isBinder && liesWithin command ti.stx
  let some (firstContext, firstInfo) := infos[0]? | return #[]
  let some head ← (try runTermElabAtTermInfo firstContext firstInfo (equationSideHead? equation rightToLeft)
      catch _ => pure none) | return #[]
  let env ← getEnv
  let termKinds := ((Parser.parserExtension.getState env).categories.find? `term).map (·.kinds)
  let isTermNode (node : Syntax) :=
    node.isIdent || (!node.isOfKind ``Parser.Term.do && termKinds.any (·.contains node.getKind))
  let mayHeadLike (target : Expr) := match target.getAppFn.constName? with
    | some name => name == head || env.isProjectionFn name
    | none => false
  let targets := (oneInfoPerRange (infos.filter (mayHeadLike ·.2.expr)))
    |>.qsort fun (_, wider) (_, narrower) => rangeSize wider.stx > rangeSize narrower.stx
  let mut rewrites : Array (Syntax × Syntax) := #[]
  for (ci, ti) in targets do
    if rewrites.any fun (rewritten, _) => liesWithin rewritten ti.stx then continue
    let node := sourceNodeAt command ti.stx
    unless isTermNode node do continue
    let pieceCandidates := infos.filter fun (_, inner) => liesWithin node inner.stx && !sameRange inner.stx node
    let attempt : TermElabM (Option Syntax) := withRef node do
      unless ← headsLike head (← instantiateMVars ti.expr) do return none
      let some found ← matchEquationSide equation rightToLeft pieceCandidates ti.expr | return none
      let pieces := found.pieces.map (sourceNodeAt command)
      let some printed ← delaboratedEquationSide equation rightToLeft pieces | return none
      let some replacement := spliceSourcePieces printed pieces | return none
      unless ← elaboratesToExpected replacement (← inferType found.expected) found.expected do return none
      return some replacement
    if let some replacement ← (try runTermElabAtTermInfo ci ti attempt catch _ => pure none) then
      rewrites := rewrites.push (node, replacement)
  return rewrites

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
private meta def ppExprFix? (ci : ContextInfo) (lctx : LocalContext) (e : Expr) : CommandElabM (Option String) :=
  try return some s!"({← runInfoMetaM ci lctx (ppExpr e)})"
  catch _ => return none

meta def lspName (name : Name) : Name := `heron ++ name

end Heron
