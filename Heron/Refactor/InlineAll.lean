module

public meta import Heron.Refactor
meta import Heron.Register
public meta import Heron.Refactor.Inline
public meta import Lean.Meta.Tactic.Delta
public meta import Lean.PrettyPrinter
public meta import Lean.Server.FileWorker.Utils

public section

open Lean Elab Command Meta Heron Server Lsp

private meta def isInlineableConst (env : Environment) (name : Name) : Bool :=
  !env.isProjectionFn name && !Meta.isInstanceCore env name &&
    -- Well-founded / structural recursion compiles away the self-reference
    -- into `brecOn`/`rec` calls, so `isRecursive` alone is not enough.
    !Meta.recExt.isTagged env name &&
    match env.find? name >>= (·.value? (allowOpaque := true)) with
    | some v => !isRecursive v name
    | none => false

private meta def deltaDelab? (ci : ContextInfo) (ti : TermInfo) : CommandElabM (Option Syntax) := do
  let some expanded ← runInfoMetaM ci ti.lctx (expandConst? ti.expr) |
    return none
  try
    let delabbed ← runInfoMetaM ci ti.lctx (PrettyPrinter.delab expanded)
    return some (← `(($delabbed)))
  catch _ =>
    return none

private meta def findAndExpandUsages (trees : Array InfoTree) (declRange? : Option Syntax.Range) (constName : Name) :
    CommandElabM (Array (Syntax × Syntax)) :=
  let infos := trees.flatMap collectTermInfos
  let candidates :=
    infos.filter fun (_, ti) => outsideDeclId declRange? ti && ti.expr.getAppFn.constName? == some constName
  (deduplicateTermInfos candidates).filterMapM fun (ci, ti) => do
    let some newStx ← deltaDelab? ci ti |
      return none
    return some (ti.stx, newStx)

private meta def countUsagesPerConst (trees : Array InfoTree) (declRange? : Option Syntax.Range) (env : Environment) :
    Std.HashMap Name Nat :=
  let infos := trees.flatMap collectTermInfos
  let candidates := infos.filter fun (_, ti) => outsideDeclId declRange? ti && isInlineableUsage env ti.expr
  (deduplicateTermInfos candidates).foldl (init := { }) fun acc (_, ti) =>
    let name := ti.expr.getAppFn.constName?.getD .anonymous
    acc.insert name ((acc.getD name 0) + 1)

private structure InlineAllConstMatch where
  constName : Name
  usageReplacements : Array (Syntax × Syntax)

private meta def detectInlineAllConst (stx : Syntax) : CommandElabM (Array InlineAllConstMatch) := do
  let trees ← collectInfoTrees stx
  let declRange? := getDeclIdRange? stx
  let usageCounts := countUsagesPerConst trees declRange? (← getEnv)
  usageCounts.toArray.filterMapM fun (name, count) => do
      if count ≤ 1 then
        return none
      let repls ← findAndExpandUsages trees declRange? name
      return some { constName := name, usageReplacements := repls }

private meta instance : Refactor InlineAllConstMatch where
  name := `inlineAllConst
  description := "Inlines every use of a private definition and removes the definition; offered on the definition's name."
  kinds := #[``Lean.Parser.Command.declaration]
  detect := detectInlineAllConst
  message := fun m => m! "Inline all {m.usageReplacements.size } usages of '{m.constName}'"
  replacements := some fun m =>
    return m.usageReplacements.map fun (oldStx, newStx) =>
        { emphasizedSyntax := oldStx
          oldSyntax := oldStx
          newSyntax := newStx
          inlineViolationLabel := m! "Inline all usages of '{m.constName}'" }
  codeActionKind := "refactor.inline"

register_refactor InlineAllConstMatch

private meta def cursorOnDeclId? (params : CodeActionParams) (text : FileMap) (stx : Syntax) : Option Syntax := do
  let declIdStx ← findDeclId? stx
  guard (syntaxOverlapsRequest text params declIdStx)
  return declIdStx

private meta def buildReplacements (declIdStx : Syntax) (defStx : Syntax) (usageRepls : Array (Syntax × Syntax))
    (constName : Name) : Array Replacement :=
  let label := m! "Inline all usages of '{constName}'"
  let usages :=
    usageRepls.map fun (oldStx, newStx) =>
      { emphasizedSyntax := declIdStx, oldSyntax := oldStx
        newSyntax := newStx, inlineViolationLabel := label : Replacement }
  let defRemoval : Replacement :=
    { emphasizedSyntax := declIdStx, oldSyntax := defStx
      newSyntax := .missing, inlineViolationLabel := label }
  usages.push defRemoval

meta unsafe def inlineAllFromDefProvider : CodeActionProvider := fun params snap => do
  let doc ← RequestM.readDoc
  let some declIdStx := cursorOnDeclId? params doc.meta.text snap.stx |
    return #[]
  let some constName := declaredConstant? declIdStx (collectTermInfos snap.infoTree) |
    return #[]
  unless isInlineableConst snap.env constName && isPrivateName constName do
    return #[]
  let (allSnaps, _, isComplete) ← doc.cmdSnaps.getFinishedPrefix
  unless isComplete do
    return #[]
  let trees := allSnaps.toArray.map (·.infoTree)
  let textEdits ←
    RequestM.runCommandElabM snap do
        let usageRepls ← findAndExpandUsages trees (getDeclIdRange? snap.stx) constName
        let repls := buildReplacements declIdStx snap.stx usageRepls constName
        let fileMap ← getFileMap
        repls.filterMapM (liftCoreM <| ·.toTextEdit fileMap)
  if textEdits.isEmpty then
    return #[]
  let title := s! "Inline all usages of '{constName}'"
  return #[{
        eager := { title, kind? := "refactor.inline" }
        lazy? :=
          some
            (pure
              { title, kind? := "refactor.inline"
                edit? :=
                  some <| .ofTextDocumentEdit { textDocument := doc.versionedIdentifier, edits := textEdits } }) }]

meta initialize unsafe
  addBuiltinCodeActionProvider (lspName `refactor.inlineAllFromDefinition) inlineAllFromDefProvider
