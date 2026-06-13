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

private def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- One `cargo clippy`-style diagnostic block for a fix. -/
def renderFix (pal : Palette) (file : String) (fm : FileMap)
    (srcLines : Array String) (fix : FixRecord) : String := Id.run do
  let s := fm.lspPosToUtf8Pos fix.range.start
  let e := fm.lspPosToUtf8Pos fix.range.end
  let sp := fm.toPosition s
  let ep := fm.toPosition e
  let header := if fix.message.isEmpty then s!"applicable refactor: {fix.rule}" else fix.message
  let gw := (toString ep.line).length
  let gnum (n : Nat) : String := spaces (gw - (toString n).length) ++ toString n
  let bar := pal.blue (spaces gw ++ " |")
  let trimmed := fix.newText.trimAscii.toString
  let isDelete := trimmed.isEmpty
  let isSingle := !fix.newText.any (· == '\n')
  let helpInline :=
    if isDelete then pal.green "help: remove this"
    else if isSingle then pal.green s!"help: replace with `{trimmed}`"
    else ""
  let mut ls : Array String := #[]
  ls := ls.push (pal.warn "warning" ++ pal.bold s!": {header}")
  ls := ls.push (pal.blue (spaces gw ++ "--> ") ++ s!"{file}:{sp.line}:{sp.column + 1}")
  ls := ls.push bar
  for ln in [sp.line:ep.line + 1] do
    let lineText := srcLines.getD (ln - 1) ""
    ls := ls.push (pal.blue (gnum ln ++ " |") ++ " " ++ lineText)
    let startCol := if ln == sp.line then sp.column else 0
    let endCol := if ln == ep.line then ep.column else lineText.length
    let caret := pal.warn (String.ofList (List.replicate (max 1 (endCol - startCol)) '^'))
    let trailing := if ln == ep.line && !helpInline.isEmpty then " " ++ helpInline else ""
    ls := ls.push (bar ++ " " ++ spaces startCol ++ caret ++ trailing)
  unless isSingle || isDelete do
    ls := ls.push bar
    ls := ls.push (pal.blue (spaces gw ++ " = ") ++ pal.green "help: replace with:")
    for rl in fix.newText.splitOn "\n" do
      ls := ls.push (bar ++ "   " ++ pal.green rl)
  ls := ls.push (pal.blue (spaces gw ++ " = ") ++ pal.dim s!"note: heron::{fix.rule}")
  ls := ls.push ""
  return String.intercalate "\n" ls.toList

def fixToJson (file : String) (fm : FileMap) (fix : FixRecord) : Json :=
  let s := fm.lspPosToUtf8Pos fix.range.start
  let e := fm.lspPosToUtf8Pos fix.range.end
  let pos := fm.toPosition s
  let before := String.Pos.Raw.extract fm.source s e
  Json.mkObj
    [ ("rule", fix.rule)
    , ("message", fix.message)
    , ("file", file)
    , ("line", (pos.line : Nat))
    , ("col", (pos.column + 1 : Nat))
    , ("before", before)
    , ("after", fix.newText) ]

/-! ## Colour decision + uniform output (shared by both binaries) -/

/-- Decide whether to colourise: forced flag wins; else on for a TTY unless `NO_COLOR`/`plain`. -/
def decideColor (color : Option Bool) (plain : Bool) : IO Bool := do
  match color with
  | some b => return b && !plain
  | none =>
    let noColor := (← IO.getEnv "NO_COLOR").isSome
    return !plain && !noColor && (← (← IO.getStdout).isTty)

/-- Render `reports` per the chosen mode (`json`/`apply`/`fix`/default human). Returns the exit code. -/
def emit (reports : Array Report) (pal : Palette) (json apply fix : Bool) : IO UInt32 := do
  if apply then
    match reports[0]? with
    | some r =>
      unless reports.size == 1 do
        IO.eprintln "heron: --apply needs exactly one matching file; narrow the input or use --fix"
        return 1
      IO.print (Heron.applyEdits r.fileMap (r.fixes.map (·.edit)))
      return 0
    | none => IO.eprintln "heron: no matching file"; return 1
  if fix then
    let mut changed := 0; let mut total := 0
    for r in reports do
      let some path := r.path | continue
      unless r.fixes.isEmpty do
        let patched := Heron.applyEdits r.fileMap (r.fixes.map (·.edit))
        if patched != r.fileMap.source then
          IO.FS.writeFile path patched
          changed := changed + 1; total := total + r.fixes.size
          IO.eprintln s!"fixed {r.fixes.size} in {path}"
    IO.eprintln (pal.warn s!"heron: applied {total} fix(es) across {changed} file(s)")
    return 0
  if json then
    IO.println (Json.arr (reports.flatMap fun r => r.fixes.map (fixToJson r.label r.fileMap))).compress
  else
    let mut total := 0
    for r in reports do
      total := total + r.fixes.size
      let srcLines := r.fileMap.source.splitOn "\n" |>.toArray
      for f in r.fixes do
        IO.println (renderFix pal r.label r.fileMap srcLines f)
    IO.eprintln (pal.warn s!"heron: {total} fix(es) across {reports.size} file(s)")
  return 0

end Reporter
