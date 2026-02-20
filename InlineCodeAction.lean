import Lean.Server.CodeActions
import Lean.Server.InfoUtils
import Lean.Server.Requests
import Lean.Meta.Tactic.Delta
import Lean.PrettyPrinter

namespace InlineCodeAction

open Lean Elab Server RequestM Lsp Meta

private def syntaxSpan (stx : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) := do
  let s ← stx.getPos? true
  let e ← stx.getTailPos? true
  return (s, e)

private def containsCursor (stx : Syntax) (cursorPos : String.Pos.Raw) : Bool :=
  match syntaxSpan stx with
  | some (s, e) => s <= cursorPos && cursorPos <= e
  | none => false

/-- Strip internal `_private.Module.N.` prefix from a name to get the user-facing part. -/
private def userFacingName : Name → Name
  | .str pre s => .str (userFacingName pre) s
  | .num _ _ => .anonymous
  | .anonymous => .anonymous

/-- Find the `declId` syntax node inside a command, if present. -/
private partial def findDeclId? (stx : Syntax) : Option Syntax :=
  if stx.isOfKind ``Lean.Parser.Command.declId then some stx
  else stx.getArgs.findSome? findDeclId?

/-- Check whether an expression references a given constant (used for recursion detection). -/
private def isRecursive (value : Expr) (name : Name) : Bool :=
  value.find? (fun e => e.isConst && e.constName? == some name) |>.isSome

/-- Collect TermInfos from an InfoTree. -/
private def collectTermInfos (tree : InfoTree) : Array (ContextInfo × TermInfo) :=
  tree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofTermInfo ti => acc.push (ctx, ti)
    | _ => acc

/-- Among candidates, pick the one with the most applied arguments. -/
private def pickMostApplied (xs : Array (ContextInfo × TermInfo)) :
    Option (ContextInfo × TermInfo) :=
  xs.foldl (init := none) fun best pair =>
    match best with
    | none => some pair
    | some (_, bestTi) =>
      if pair.2.expr.getAppNumArgs > bestTi.expr.getAppNumArgs then some pair else best

/-- Among candidates, pick the one with the smallest syntax range. -/
private def pickSmallest (xs : Array (ContextInfo × TermInfo)) :
    Option (ContextInfo × TermInfo) :=
  xs.foldl (init := none) fun best pair =>
    let dominated := match best with
      | none => true
      | some (_, bestTi) =>
        match syntaxSpan pair.2.stx, syntaxSpan bestTi.stx with
        | some (s, e), some (bs, be) =>
          e.byteIdx - s.byteIdx < be.byteIdx - bs.byteIdx
        | some _, none => true
        | _, _ => false
    if dominated then some pair else best

/-- Deduplicate usages: for each distinct start position keep the most-applied,
    skipping any usage whose position falls inside `declIdRange?`. -/
private def deduplicateUsages
    (usages : Array (ContextInfo × TermInfo))
    (declIdRange? : Option (String.Pos.Raw × String.Pos.Raw))
    : Array (ContextInfo × TermInfo) :=
  let filtered := usages.filter fun (_, ti) =>
    match declIdRange?, ti.stx.getPos? true with
    | some (ds, de), some pos => !(ds <= pos && pos < de)
    | _, _ => true
  -- For each start position, keep only the candidate with the most applied args
  filtered.foldl (init := #[]) fun acc (ci, ti) =>
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

/-- Find the const at the cursor, returning its internal name if it has a value. -/
private def findConstAtCursor
    (infos : Array (ContextInfo × TermInfo))
    (env : Environment)
    (cursorPos : String.Pos.Raw)
    : Option Name := do
  let constsAtCursor := infos.filter fun (_, ti) =>
    containsCursor ti.stx cursorPos && ti.expr.isConst &&
    match ti.expr.constName? with
    | some name => match env.find? name with
      | some cinfo => cinfo.hasValue
      | none => false
    | none => false
  let (_, constTi) ← pickSmallest constsAtCursor
  constTi.expr.constName?

@[code_action_provider]
def inlineProvider : CodeActionProvider := fun params snap => do
  let doc ← readDoc
  let text := doc.meta.text
  let cursorPos := text.lspPosToUtf8Pos params.range.start
  let infos := collectTermInfos snap.infoTree
  let env := snap.env
  let mut actions : Array LazyCodeAction := #[]

  let declId? := findDeclId? snap.stx
  let cursorOnDeclId := match declId? with
    | some declId => containsCursor declId cursorPos
    | none => false

  if cursorOnDeclId then
    -- Inline definition: replace ALL usages in the file, delete the definition
    if let some targetName := findConstAtCursor infos env cursorPos then
      if let some cinfo := env.find? targetName then
        if let some value := cinfo.value? then
          if !isRecursive value targetName then
            let displayName := userFacingName targetName
            let eager : CodeAction := {
              title := s!"Inline definition of '{displayName}'"
              kind? := some "refactor.inline"
            }
            actions := actions.push {
              eager
              lazy? := some do
                let (snapList, _, _) ← doc.cmdSnaps.getFinishedPrefix
                let mut allEdits : Array TextEdit := #[]
                for otherSnap in snapList.toArray do
                  let declIdRange := findDeclId? otherSnap.stx |>.bind syntaxSpan
                  let otherInfos := collectTermInfos otherSnap.infoTree
                  let usages := otherInfos.filter fun (_, ti) =>
                    ti.expr.getAppFn.constName? == some targetName
                  let deduped := deduplicateUsages usages declIdRange
                  for (ci, ti) in deduped do
                    match ← ci.runMetaM ti.lctx (delta? ti.expr) with
                    | some result =>
                      let newText ← ci.runMetaM ti.lctx do
                        return s!"({← ppExpr result})"
                      if let some (s, e) := syntaxSpan ti.stx then
                        allEdits := allEdits.push {
                          range := text.utf8RangeToLspRange ⟨s, e⟩
                          newText
                        }
                    | none => pure ()
                -- Delete the definition command
                if let some (defStart, defEnd) := syntaxSpan snap.stx then
                  allEdits := allEdits.push {
                    range := text.utf8RangeToLspRange ⟨defStart, defEnd⟩
                    newText := ""
                  }
                return { eager with
                  edit? := some <| .ofTextDocumentEdit {
                    textDocument := doc.versionedIdentifier
                    edits := allEdits
                  }
                }
            }
  else
    -- Inline call: replace just this one usage
    if let some targetName := findConstAtCursor infos env cursorPos then
      let appCandidates := infos.filter fun (_, ti) =>
        containsCursor ti.stx cursorPos &&
        ti.expr.getAppFn.constName? == some targetName
      if let some (ci, ti) := pickMostApplied appCandidates then
        let displayName := userFacingName targetName
        let eager : CodeAction := {
          title := s!"Inline '{displayName}'"
          kind? := some "refactor.inline"
        }
        actions := actions.push {
          eager
          lazy? := some do
            let some result ← ci.runMetaM ti.lctx (delta? ti.expr)
              | return eager
            let newText ← ci.runMetaM ti.lctx do
              return s!"({← ppExpr result})"
            let some (stxStart, stxEnd) := syntaxSpan ti.stx | return eager
            return { eager with
              edit? := some <| .ofTextEdit doc.versionedIdentifier {
                range := text.utf8RangeToLspRange ⟨stxStart, stxEnd⟩
                newText
              }
            }
        }

  -- Inline let-binding
  let letCandidates := infos.filter fun (_, ti) =>
    containsCursor ti.stx cursorPos && ti.expr.isLet
  if let some (ci, ti) := pickSmallest letCandidates then
    if let .letE name _ value body _ := ti.expr then
      let eager : CodeAction := {
        title := s!"Inline let '{name}'"
        kind? := some "refactor.inline"
      }
      actions := actions.push {
        eager
        lazy? := some do
          let newText ← ci.runMetaM ti.lctx do
            return s!"({← ppExpr (body.instantiate1 value)})"
          let some (stxStart, stxEnd) := syntaxSpan ti.stx | return eager
          return { eager with
            edit? := some <| .ofTextEdit doc.versionedIdentifier {
              range := text.utf8RangeToLspRange ⟨stxStart, stxEnd⟩
              newText
            }
          }
      }

  return actions

end InlineCodeAction
