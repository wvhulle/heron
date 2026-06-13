module

public import Lean.Data.Lsp.Basic
public import Lean.Data.Lsp.Utf16
public import Lean.Data.Json
public import Lean.Data.Position

public section

open Lean

namespace Heron

/-- The serializable plugin→reporter sink DTO: one suggested fix plus the rule metadata
needed to render it, in a form that round-trips through JSON. Produced by
`Heron.collectFixRecords` — written to the build sink during a `lake build` (when
`HERON_FIX_DIR` is set) by the always-on linter, and read back by the reporter binaries.

This lives in the core plugin library (not in `Reporter/`) only because its *producer*
runs inside the build-time linter, which is part of the plugin `.so`. The LSP path does
not use it: code actions go `Replacement → Lsp.TextEdit` directly, in-process.

`before` text and screen positions are recomputed from the source + `edit.range` at
render time, so they are intentionally not stored. -/
structure FixRecord where
  /-- Rule name, e.g. `funToCdot`. -/
  rule : String
  /-- The rule's headline message. -/
  message : String
  /-- The replacement to apply: range to replace + new text, in LSP coordinates
  (empty `newText` ⇒ deletion). -/
  edit : Lsp.TextEdit
  /-- Detailed explanation (hover popup body). Empty ⇒ none. -/
  explanation : String := ""
  /-- Reference topic shown in parentheses. Empty ⇒ no reference. -/
  referenceTopic : String := ""
  /-- Reference URL. Empty ⇒ no reference. -/
  referenceUrl : String := ""
  deriving ToJson, FromJson

/-- Apply non-overlapping LSP `TextEdit`s to a source string. Edits are sorted by range start
descending and applied back-to-front so earlier byte offsets stay valid (LSP ranges refer to the
original document). Shared by `Heron.Assert`, the build sink, and the `heron-lint` tool. -/
def applyEdits (text : FileMap) (edits : Array Lsp.TextEdit) : String :=
  let sorted := edits.qsort fun a b => text.lspPosToUtf8Pos b.range.start < text.lspPosToUtf8Pos a.range.start
  sorted.foldl
    (init :=
    text.source)
    fun src edit =>
    let startPos := text.lspPosToUtf8Pos edit.range.start
    let endPos := text.lspPosToUtf8Pos edit.range.end
    let pre := String.Pos.Raw.extract src 0 startPos
    let post := String.Pos.Raw.extract src endPos src.rawEndPos
    pre ++ edit.newText ++ post

end Heron
