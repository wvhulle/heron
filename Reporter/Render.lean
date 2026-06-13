import Lean
import Heron.Fix

/-! Shared output for the fix reporters: the `Report` type and the cargo-clippy-style / JSON
renderers. Operates on `Heron.FixRecord` so every engine (per-file, shared-env, build-sink)
renders identically. -/

open Lean Heron

namespace Reporter

/-- A file's findings, with the `FileMap` of its current source for rendering/applying. -/
structure Report where
  /-- Path on disk, or `none` for stdin (not rewritable by `--fix`). -/
  path : Option String
  label : String
  fileMap : FileMap
  fixes : Array FixRecord

/-! ## ANSI palette -/

structure Palette where
  on : Bool

private def esc : String := String.ofList [Char.ofNat 27]

def Palette.code (p : Palette) (c s : String) : String :=
  if p.on then s!"{esc}[{c}m{s}{esc}[0m" else s

def Palette.warn (p : Palette) (s : String) : String := p.code "1;33" s
def Palette.blue (p : Palette) (s : String) : String := p.code "1;34" s
def Palette.green (p : Palette) (s : String) : String := p.code "1;32" s
def Palette.bold (p : Palette) (s : String) : String := p.code "1" s
def Palette.dim (p : Palette) (s : String) : String := p.code "2" s
/-- Italic, used for replacement text so it reads as the suggested code, not the source. -/
def Palette.italic (p : Palette) (s : String) : String := p.code "3" s
/-- Dim italic, used for the `replace with` label so it reads with the replacement. -/
def Palette.dimItalic (p : Palette) (s : String) : String := p.code "2;3" s
/-- Underlined cyan, used for URLs so they stand out as links. -/
def Palette.url (p : Palette) (s : String) : String := p.code "4;36" s

/-- Wrap `text` in an OSC 8 hyperlink to `url` (so terminals that support it make it
clickable), gated on the same `on` flag as colour. Empty `url` ⇒ plain text. -/
private def osc8 (on : Bool) (url text : String) : String :=
  if on && !url.isEmpty then s!"{esc}]8;;{url}{esc}\\{text}{esc}]8;;{esc}\\" else text

private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- Pre-computed framing shared by every line of one diagnostic block: the blank-gutter
`bar`/`eq` leads and the line-number column, sized to the widest line shown. -/
private structure Gutter where
  pal : Palette
  width : Nat

/-- The `|` continuation gutter (blank line-number column). -/
private def Gutter.bar (g : Gutter) : String := g.pal.blue (spaces g.width ++ " |")
/-- The `=` lead used for the metadata notes. -/
private def Gutter.eq (g : Gutter) : String := g.pal.blue (spaces g.width ++ " = ")
/-- A right-aligned line number followed by the `|` gutter. -/
private def Gutter.num (g : Gutter) (n : Nat) : String :=
  g.pal.blue (spaces (g.width - (toString n).length) ++ toString n ++ " |")

/-- The classified replacement: whether it deletes, and whether it is short enough to
annotate inline beside the caret rather than in a block below. -/
private structure Suggestion where
  newText : String
  trimmed : String
  isDelete : Bool
  inlineFix : Bool

/-- Classify an edit's replacement text. Short single-line replacements ride the caret
line; long or multi-line ones go in a block below to avoid wrapping. -/
private def Suggestion.of (newText : String) : Suggestion :=
  let trimmed := newText.trimAscii.toString
  let isDelete := trimmed.isEmpty
  let isSingle := !newText.any (· == '\n')
  { newText, trimmed, isDelete, inlineFix := isSingle && !isDelete && trimmed.length ≤ 40 }

/-- The annotation appended to the caret line (empty unless this is a delete or a short
inline replacement). -/
private def Suggestion.inlineHelp (s : Suggestion) (pal : Palette) : String :=
  if s.isDelete then " " ++ pal.dim "remove this"
  else if s.inlineFix then " " ++ pal.dimItalic "replace with " ++ pal.italic s!"`{s.trimmed}`"
  else ""

/-- The replacement block for multi-line / long single-line fixes, set off by a leading
blank line (`[]` for deletes and inline fixes). -/
private def Suggestion.block (s : Suggestion) (g : Gutter) : List String :=
  if s.isDelete || s.inlineFix then []
  else "" :: (g.eq ++ g.pal.dimItalic "replace with:")
    :: (s.newText.splitOn "\n").map (fun rl => g.bar ++ "   " ++ g.pal.italic rl)

/-- The opening lines: `warning: <message> [heron::rule]`, the `--> file:line:col`
location (a clickable OSC 8 link pointing at the exact line:col), and the leading bar. -/
private def headerLines (g : Gutter) (file fileUri : String) (fix : FixRecord) (sp : Position) :
    List String :=
  let header := if fix.message.isEmpty then s!"applicable refactor: {fix.rule}" else fix.message
  let lineCol := s!"{sp.line}:{sp.column + 1}"
  let target := if fileUri.isEmpty then "" else s!"{fileUri}:{lineCol}"
  [ g.pal.warn "warning" ++ g.pal.bold s!": {header}" ++ " " ++ g.pal.dim s!"[heron::{fix.rule}]"
  , g.pal.blue (spaces g.width ++ "--> ") ++ osc8 g.pal.on target (g.pal.url s!"{file}:{lineCol}")
  , g.bar ]

/-- One source line, plus a caret row underlining the span when `ln` falls within
`[sp.line, ep.line]`. The inline help rides the caret on the final span line. -/
private def sourceLine (g : Gutter) (sp ep : Position) (lineText : String) (ln : Nat)
    (inlineHelp : String) : List String :=
  let src := g.num ln ++ " " ++ lineText
  if sp.line ≤ ln && ln ≤ ep.line then
    let startCol := if ln == sp.line then sp.column else 0
    let endCol := if ln == ep.line then ep.column else lineText.length
    let caret := g.pal.warn (String.ofList (List.replicate (max 1 (endCol - startCol)) '^'))
    let trailing := if ln == ep.line then inlineHelp else ""
    [src, g.bar ++ " " ++ spaces startCol ++ caret ++ trailing]
  else [src]

/-- The hover-popup detail, preceded by a blank line: the explanation `note` (or the rule
id when absent), an optional reference, and the disable hint. -/
private def notesLines (g : Gutter) (fix : FixRecord) : List String :=
  let note :=
    if fix.explanation.isEmpty then g.eq ++ g.pal.bold "note: " ++ g.pal.dim s!"heron::{fix.rule}"
    else g.eq ++ g.pal.bold "note: " ++ g.pal.dim fix.explanation
  let refs : List String :=
    if fix.referenceUrl.isEmpty then []
    else
      let topic := if fix.referenceTopic.isEmpty then "" else g.pal.dim s!" ({fix.referenceTopic})"
      [g.eq ++ g.pal.bold "reference: " ++ osc8 g.pal.on fix.referenceUrl (g.pal.url fix.referenceUrl) ++ topic]
  let help := g.eq ++ g.pal.bold "help: " ++ g.pal.dim s!"disable with `set_option linter.{fix.rule} false`"
  ("" :: note :: refs) ++ [help]

/-- One `cargo clippy`-style diagnostic block for a fix. -/
def renderFix (pal : Palette) (file fileUri : String) (fm : FileMap)
    (srcLines : Array String) (fix : FixRecord) : String :=
  let sp := fm.toPosition (fm.lspPosToUtf8Pos fix.edit.range.start)
  let ep := fm.toPosition (fm.lspPosToUtf8Pos fix.edit.range.end)
  -- Show two lines of source on each side of the span for orientation.
  let ctx := 2
  let firstLn := max 1 (sp.line - ctx)
  let lastLn := min srcLines.size (ep.line + ctx)
  let g : Gutter := { pal, width := (toString lastLn).length }
  let sugg := Suggestion.of fix.edit.newText
  let inlineHelp := sugg.inlineHelp pal
  let source := (List.range' firstLn (lastLn + 1 - firstLn)).flatMap fun ln =>
    sourceLine g sp ep (srcLines.getD (ln - 1) "") ln inlineHelp
  String.intercalate "\n"
    (headerLines g file fileUri fix sp ++ source ++ sugg.block g ++ notesLines g fix ++ [""])

def fixToJson (file : String) (fm : FileMap) (fix : FixRecord) : Json :=
  let s := fm.lspPosToUtf8Pos fix.edit.range.start
  let e := fm.lspPosToUtf8Pos fix.edit.range.end
  let pos := fm.toPosition s
  let before := String.Pos.Raw.extract fm.source s e
  Json.mkObj
    [ ("rule", fix.rule)
    , ("message", fix.message)
    , ("file", file)
    , ("line", (pos.line : Nat))
    , ("col", (pos.column + 1 : Nat))
    , ("before", before)
    , ("after", fix.edit.newText) ]

/-! ## Colour decision + uniform output (shared by both binaries) -/

/-- Decide whether to colourise: forced flag wins; else on for a TTY unless `NO_COLOR`/`plain`. -/
def decideColor (color : Option Bool) (plain : Bool) : IO Bool := do
  match color with
  | some b => return b && !plain
  | none =>
    let noColor := (← IO.getEnv "NO_COLOR").isSome
    return !plain && !noColor && (← (← IO.getStdout).isTty)

/-- The `file://` URI for a report's on-disk path (absolute if it resolves), or empty for
stdin. The lone IO needed by the human renderer, isolated here. -/
private def absFileUri : Option String → IO String
  | none => pure ""
  | some p => do
    let abs ← (try IO.FS.realPath p catch _ => pure (System.FilePath.mk p))
    return s!"file://{abs}"

/-- Apply every report's fixes to disk, returning the number of fixes applied per file that
actually changed. -/
private def applyReports (reports : Array Report) : IO (Array Nat) :=
  reports.filterMapM fun r => do
    let some path := r.path | return none
    if r.fixes.isEmpty then return none
    let patched := Heron.applyEdits r.fileMap (r.fixes.map (·.edit))
    if patched == r.fileMap.source then return none
    IO.FS.writeFile path patched
    IO.eprintln s!"fixed {r.fixes.size} in {path}"
    return some r.fixes.size

/-- Render `reports` per the chosen mode (`json`/`apply`/`fix`/default human). Returns the exit code. -/
def emit (reports : Array Report) (pal : Palette) (json apply fix : Bool) : IO UInt32 := do
  if apply then
    let some r := reports[0]? | do IO.eprintln "heron: no matching file"; return 1
    unless reports.size == 1 do
      IO.eprintln "heron: --apply needs exactly one matching file; narrow the input or use --fix"
      return 1
    IO.print (Heron.applyEdits r.fileMap (r.fixes.map (·.edit)))
    return 0
  if fix then
    let applied ← applyReports reports
    IO.eprintln (pal.warn s!"heron: applied {applied.sum} fix(es) across {applied.size} file(s)")
    return 0
  if json then
    IO.println (Json.arr (reports.flatMap fun r => r.fixes.map (fixToJson r.label r.fileMap))).compress
    return 0
  reports.forM fun r => do
    let srcLines := r.fileMap.source.splitOn "\n" |>.toArray
    let fileUri ← absFileUri r.path
    r.fixes.forM fun f => IO.println (renderFix pal r.label fileUri r.fileMap srcLines f)
  IO.eprintln (pal.warn s!"heron: {(reports.map (·.fixes.size)).sum} fix(es) across {reports.size} file(s)")
  return 0

end Reporter
