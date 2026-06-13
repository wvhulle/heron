module

public import Lean.Data.Lsp.Basic
public import Lean.Data.Lsp.Utf16
public import Lean.Data.Json
public import Lean.Data.Position

public section

open Lean

namespace Heron

/-- A single suggested fix, in a form that round-trips through the build sink and is consumed by
the `heron-lint` tool. This is the canonical sink schema — produced by `Heron.collectFixRecords`
(during a build, when `HERON_FIX_DIR` is set) and read back by the tool. Positions/`before` text
are derived from the source + `range` at render time, so they are intentionally not stored. -/
structure FixRecord where
  /-- Rule name, e.g. `funToCdot`. -/
  rule : String
  /-- The rule's headline message. -/
  message : String
  /-- Source range to replace (LSP coordinates). -/
  range : Lsp.Range
  /-- Replacement text (empty ⇒ deletion). -/
  newText : String
  deriving Repr, Inhabited, ToJson, FromJson

/-- The LSP `TextEdit` for this record (range + replacement). -/
def FixRecord.edit (f : FixRecord) : Lsp.TextEdit := { range := f.range, newText := f.newText }

/-- Apply non-overlapping LSP `TextEdit`s to a source string. Edits are sorted by range start
descending and applied back-to-front so earlier byte offsets stay valid (LSP ranges refer to the
original document). Shared by `Heron.Assert`, the build sink, and the `heron-lint` tool. -/
def applyEdits (text : FileMap) (edits : Array Lsp.TextEdit) : String :=
  let sorted := edits.qsort fun a b =>
    text.lspPosToUtf8Pos b.range.start < text.lspPosToUtf8Pos a.range.start
  sorted.foldl (init := text.source) fun src edit =>
    let startPos := text.lspPosToUtf8Pos edit.range.start
    let endPos := text.lspPosToUtf8Pos edit.range.end
    let pre := String.Pos.Raw.extract src 0 startPos
    let post := String.Pos.Raw.extract src endPos src.rawEndPos
    pre ++ edit.newText ++ post

end Heron
