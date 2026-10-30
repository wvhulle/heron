module

public import Lean.Data.Lsp.Basic
public import Lean.Data.Lsp.Utf16
public import Lean.Data.Json
public import Lean.Data.Position
public import Heron.Source

public section

open Lean

namespace Heron

/-- The serializable plugin→reporter sink DTO: one suggested fix plus the rule metadata
needed to render it, in a form that round-trips through JSON. Produced by
`Heron.collectFixRecords` — written to the build sink during a `lake build` (when
`HERON_FIX_DIR` is set) by the always-on linter, and read back by the reporter binaries.

This lives in the core plugin library (not in `FixReporting/`) only because its *producer*
runs inside the build-time linter, which is part of the plugin `.so`. The LSP path does
not use it: code actions go `Replacement → Lsp.TextEdit` directly, in-process.

`before` text and screen positions are recomputed from the source + `span` at
render time, so they are intentionally not stored. -/
structure FixRecord where
  /-- Rule name, e.g. `singleUseLambdaToCdotFunction`. -/
  rule : String
  /-- The rule's headline message. -/
  message : String
  span : Lsp.Range
  edits : Array Lsp.TextEdit := #[]
  /-- Detailed explanation (hover popup body). Empty ⇒ none. -/
  explanation : String := ""
  sources : Array SourceLink := #[]
  deriving ToJson, FromJson

def applyEdits (text : FileMap) (edits : Array Lsp.TextEdit) : String :=
  let sorted := edits.qsort fun a b => text.lspPosToUtf8Pos b.range.start < text.lspPosToUtf8Pos a.range.start
  let (patched, _) := sorted.foldl (init := (text.source, text.source.rawEndPos))
    fun (src, firstAppliedStart) edit =>
      let startPos := text.lspPosToUtf8Pos edit.range.start
      let endPos := text.lspPosToUtf8Pos edit.range.end
      if firstAppliedStart < endPos then (src, firstAppliedStart)
      else (String.Pos.Raw.extract src 0 startPos ++ edit.newText ++ String.Pos.Raw.extract src endPos src.rawEndPos,
            startPos)
  patched

def editsOverlap (text : FileMap) (first second : Lsp.TextEdit) : Bool :=
  let firstStart := text.lspPosToUtf8Pos first.range.start
  let firstEnd := text.lspPosToUtf8Pos first.range.end
  let secondStart := text.lspPosToUtf8Pos second.range.start
  let secondEnd := text.lspPosToUtf8Pos second.range.end
  firstStart == secondStart || (firstStart < secondEnd && secondStart < firstEnd)

def applyFixes (text : FileMap) (fixes : Array (Array Lsp.TextEdit)) : String :=
  let acceptedEdits := fixes.foldl (init := #[]) fun accepted fixEdits =>
    if fixEdits.any fun edit => accepted.any (editsOverlap text edit) then accepted
    else accepted ++ fixEdits
  applyEdits text acceptedEdits

def editsSpan (text : FileMap) (edits : Array Lsp.TextEdit) : Option Lsp.Range :=
  edits.foldl (init := none) fun span? edit =>
    match span? with
    | none => some edit.range
    | some span =>
      let start := if text.lspPosToUtf8Pos edit.range.start < text.lspPosToUtf8Pos span.start
        then edit.range.start else span.start
      let stop := if text.lspPosToUtf8Pos span.end < text.lspPosToUtf8Pos edit.range.end
        then edit.range.end else span.end
      some { start, «end» := stop }

def editedSpanText (text : FileMap) (fix : FixRecord) : Option String :=
  if fix.edits.isEmpty then none else
    let patched := applyEdits text fix.edits
    let spanStart := text.lspPosToUtf8Pos fix.span.start
    let spanEnd := text.lspPosToUtf8Pos fix.span.end
    let growth : Int := patched.rawEndPos.byteIdx - text.source.rawEndPos.byteIdx
    let patchedEnd : Nat := ((spanEnd.byteIdx : Int) + growth).toNat
    some (String.Pos.Raw.extract patched spanStart ⟨patchedEnd⟩)

end Heron
