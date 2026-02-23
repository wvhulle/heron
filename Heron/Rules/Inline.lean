import Heron.AssertEdits
import Lean.Meta.Tactic.Delta
import Lean.PrettyPrinter
import Lean.Meta.Hint

open Lean Elab Command Meta

private def linterInline : Lean.Option Bool := { name := `linter.inline, defValue := false }

private structure InlineFixData where
  stx : Syntax
  newText : String

private def syntaxSpan (stx : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) := do
  let s ← stx.getPos? true
  let e ← stx.getTailPos? true
  return (s, e)

private def collectTermInfos (tree : InfoTree) : Array (ContextInfo × TermInfo) :=
  tree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofTermInfo ti => acc.push (ctx, ti)
    | _ => acc

private def deduplicateByPosition
    (usages : Array (ContextInfo × TermInfo))
    : Array (ContextInfo × TermInfo) :=
  usages.foldl (init := #[]) fun acc (ci, ti) =>
    match ti.stx.getPos? true with
    | some pos =>
      let dominated := acc.any fun (_, old) =>
        old.stx.getPos? true == some pos && old.expr.getAppNumArgs >= ti.expr.getAppNumArgs
      if dominated then acc
      else
        let acc := acc.filter fun (_, old) =>
          !(old.stx.getPos? true == some pos && old.expr.getAppNumArgs < ti.expr.getAppNumArgs)
        acc.push (ci, ti)
    | none => acc

private def isRecursive (value : Expr) (name : Name) : Bool :=
  value.find? (fun e => e.isConst && e.constName? == some name) |>.isSome

private def collectElabInfoTrees (stx : Syntax) : CommandElabM (Array InfoTree) := do
  let savedInfoState ← getInfoState
  let savedMessages := (← get).messages
  let savedLinters ← lintersRef.get
  setInfoState { enabled := true, trees := {} }
  lintersRef.set #[]
  try withoutModifyingEnv do
    withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
      withReader ({ · with snap? := none }) do
        elabCommand stx
  catch _ => pure ()
  let trees := (← getInfoState).trees.toArray
  setInfoState savedInfoState
  modify fun s => { s with messages := savedMessages }
  lintersRef.set savedLinters
  return trees

private def runInfoMetaM (ci : ContextInfo) (lctx : LocalContext) (x : MetaM α) : CommandElabM α := do
  match ← (ci.runMetaM lctx x).toBaseIO with
  | .ok a => return a
  | .error e => throwError "{e}"

private def detectInlineOpportunities (stx : Syntax) : CommandElabM (Array InlineFixData) := do
  let trees ← collectElabInfoTrees stx
  let env ← getEnv
  let infos := trees.flatMap collectTermInfos
  let mut fixes : Array InlineFixData := #[]
  -- Inline const applications
  let constUsages := infos.filter fun (_, ti) =>
    ti.expr.getAppFn.isConst &&
    match ti.expr.getAppFn.constName? with
    | some name =>
      !env.isProjectionFn name &&
      !Meta.isInstanceCore env name &&
      match env.find? name with
      | some cinfo => match cinfo.value? with
        | some value => !isRecursive value name
        | none => false
      | none => false
    | none => false
  let deduped := deduplicateByPosition constUsages
  for (ci, ti) in deduped do
    try
      let result ← runInfoMetaM ci ti.lctx (delta? ti.expr)
      if let some expanded := result then
        let newText ← runInfoMetaM ci ti.lctx do
          return s!"({← ppExpr expanded})"
        fixes := fixes.push { stx := ti.stx, newText }
    catch _ => pure ()
  -- Inline let-bindings
  let letCandidates := infos.filter fun (_, ti) => ti.expr.isLet
  for (ci, ti) in letCandidates do
    if let .letE _ _ value body _ := ti.expr then
      try
        let newText ← runInfoMetaM ci ti.lctx do
          return s!"({← ppExpr (body.instantiate1 value)})"
        fixes := fixes.push { stx := ti.stx, newText }
      catch _ => pure ()
  return fixes

private def toSuggestion (data : InlineFixData) : Hint.Suggestion :=
  { suggestion := data.newText, span? := some data.stx }

private def inlineLinter : Linter where run := withSetOptionIn fun stx => do
  unless linterInline.get (← getOptions) do return
  for fixData in ← detectInlineOpportunities stx do
    let hint ← liftCoreM <| MessageData.hint m!"Can be inlined." #[toSuggestion fixData]
    Linter.logLint linterInline fixData.stx (m!"Inline." ++ hint)

#eval addLinter inlineLinter

/-! ## Tests -/

def double (n : Nat) := n + n

#assertEdits inline `(term| double 3) => `(term| (3 + 3)) in
example : Nat := double 3

def myConst := 42

#assertEdits inline `(term| myConst) => `(term| (42)) in
example : Nat := myConst
