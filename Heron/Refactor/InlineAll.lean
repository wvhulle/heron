import Heron.Refactor
import Heron.Refactor.Inline
import Heron.Assert
import Lean.Meta.Tactic.Delta
import Lean.PrettyPrinter
import Lean.Server.FileWorker.Utils

open Lean Elab Command Meta Heron Server Lsp

private def isInlineableConst (env : Environment) (name : Name) : Bool :=
  !env.isProjectionFn name && !Meta.isInstanceCore env name &&
    match env.find? name >>= (·.value?) with
    | some v => !isRecursive v name
    | none => false

private def resolveConstName? (infos : Array (ContextInfo × TermInfo)) (declIdStx : Syntax) (ns : Name) : Option Name :=
  do
  let pos ← declIdStx.getPos? true
  match infos.find? fun (_, ti) => ti.stx.getPos? true == some pos with
  | some (_, ti) =>
    ti.expr.constName?
  | none =>
    some (ns ++ declIdStx[0]!.getId)

private def deltaDelab? (ci : ContextInfo) (ti : TermInfo) : CommandElabM (Option Syntax) := do
  let some expanded ← runInfoMetaM ci ti.lctx (delta? ti.expr) |
    return none
  try
    let delabbed ← runInfoMetaM ci ti.lctx (PrettyPrinter.delab expanded)
    return some (← `(($delabbed)))
  catch _ =>
    return none

private def findAndExpandUsages (trees : Array InfoTree) (declRange? : Option Syntax.Range) (constName : Name) :
    CommandElabM (Array (Syntax × Syntax)) :=
  let infos := trees.flatMap collectTermInfos
  let candidates :=
    infos.filter fun (_, ti) => outsideDeclId declRange? ti && ti.expr.getAppFn.constName? == some constName
  (deduplicateTermInfos candidates).filterMapM fun (ci, ti) => do
    let some newStx ← deltaDelab? ci ti |
      return none
    return some (ti.stx, newStx)

private def countUsagesPerConst (trees : Array InfoTree) (declRange? : Option Syntax.Range) (env : Environment) :
    Std.HashMap Name Nat :=
  let infos := trees.flatMap collectTermInfos
  let candidates := infos.filter fun (_, ti) => outsideDeclId declRange? ti && isInlineableUsage env ti.expr
  (deduplicateTermInfos candidates).foldl (init := { }) fun acc (_, ti) =>
    let name := ti.expr.getAppFn.constName?.getD .anonymous
    acc.insert name ((acc.getD name 0) + 1)

private structure InlineAllConstMatch where
  constName : Name
  usageReplacements : Array (Syntax × Syntax)

private def detectInlineAllConst (stx : Syntax) : CommandElabM (Array InlineAllConstMatch) := do
  let trees ← collectInfoTrees stx
  let declRange? := getDeclIdRange? stx
  let usageCounts := countUsagesPerConst trees declRange? (← getEnv)
  usageCounts.toArray.filterMapM fun (name, count) => do
      if count ≤ 1 then 
        return none
      let repls ← findAndExpandUsages trees declRange? name
      return some { constName := name, usageReplacements := repls }

@[refactor_rule]
instance : Refactor InlineAllConstMatch where
  name := `inlineAllConst
  detect := detectInlineAllConst
  message := fun m => m! "Inline all {m.usageReplacements.size } usages of '{m.constName}'"
  replacements := fun m =>
    return m.usageReplacements.map fun (oldStx, newStx) =>
        { emphasizedSyntax := oldStx
          oldSyntax := oldStx
          newSyntax := newStx
          inlineViolationLabel := m! "Inline all usages of '{m.constName}'" }
  codeActionKind := "refactor.inline"

private def cursorOnDeclId? (params : CodeActionParams) (text : FileMap) (stx : Syntax) : Option Syntax := do
  let declIdStx ← findDeclId? stx
  let declIdRange ← declIdStx.getRange?
  let startPos := text.lspPosToUtf8Pos params.range.start
  let endPos := text.lspPosToUtf8Pos params.range.end
  guard (declIdRange.start ≤ endPos && startPos ≤ declIdRange.stop)
  return declIdStx

private def buildReplacements (declIdStx : Syntax) (defStx : Syntax) (usageRepls : Array (Syntax × Syntax))
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

@[code_action_provider]
unsafe def inlineAllFromDefProvider : CodeActionProvider := fun params snap => do
  let doc ← RequestM.readDoc
  let some declIdStx := cursorOnDeclId? params doc.meta.text snap.stx |
    return #[]
  let snapInfos := collectTermInfos snap.infoTree
  let ns := snap.cmdState.scopes.head!.currNamespace
  let some constName := resolveConstName? snapInfos declIdStx ns |
    return #[]
  unless isInlineableConst snap.env constName do
    return #[]
  let (allSnaps, _, _) ← doc.cmdSnaps.getFinishedPrefix
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

namespace Tests

def triple (n : Nat) :=
  n + n + n

#assertRefactor inlineAllConst in
  example : Nat :=
    triple 2 + triple 3 becomes
  `(example : Nat :=
      (2 + 2 + 2) + (3 + 3 + 3))

def myVal :=
  10

#assertIgnore inlineAllConst in
  example : Nat :=
    myVal

#assertIgnore inlineAllConst in
  def unused :=
    42

#assertIgnore inlineAllConst in
  def recFn : Nat → Nat
    | 0 => 0
    | n + 1 => recFn n

end Tests
