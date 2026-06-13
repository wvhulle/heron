import Lean
import Lake
import Lake.Load.Workspace

/-!
# `heron-lint` — build-integrated fix reporter

Heron's linter runs *during* `lake build` and, when `HERON_FIX_DIR` is set, writes each module's
suggested fixes to `${HERON_FIX_DIR}/<module>.json` (see `Heron/Check.lean`). This binary drives
that build and renders the resulting sink — like `cargo clippy`, the lints come from the compile
itself, and **Lake's incremental cache decides what re-lints**. No second elaboration, no cache of
our own.

To lint every module (not only those that `import Heron`), the build loads Heron as a Lean
*plugin* via `lean --plugin`, wired in the project's lakefile and enabled by
`-KheronPlugin=<libheron_Heron.so>` (this binary passes it automatically).

    lake env heron-lint                  # build + report all fixes (clippy-style)
    lake env heron-lint Sparkle/Analog   # report only fixes under a path
    lake env heron-lint --json | jq      # machine-readable
    lake env heron-lint --fix            # rewrite files in place
    lake env heron-lint --no-build       # just read the existing sink (skip the build)

Requires a project whose lakefile honours `-KheronPlugin` (see Sparkle's `lakefile.lean`).
-/

open Lean

namespace HeronLint

/-- A single suggested edit. -/
structure Fix where
  rule : Name
  message : String
  edit : Lsp.TextEdit

/-- A file's findings, with the `FileMap` of its current source for rendering/applying. -/
structure Report where
  path : String
  fileMap : FileMap
  fixes : Array Fix

/-- Apply non-overlapping LSP `TextEdit`s back-to-front (ranges refer to the original document). -/
def applyEdits (text : FileMap) (edits : Array Lsp.TextEdit) : String :=
  let sorted := edits.qsort fun a b =>
    text.lspPosToUtf8Pos b.range.start < text.lspPosToUtf8Pos a.range.start
  sorted.foldl (init := text.source) fun src edit =>
    let startPos := text.lspPosToUtf8Pos edit.range.start
    let endPos := text.lspPosToUtf8Pos edit.range.end
    let pre := String.Pos.Raw.extract src 0 startPos
    let post := String.Pos.Raw.extract src endPos src.rawEndPos
    pre ++ edit.newText ++ post

/-! ## Sink reading -/

/-- `Sparkle.Analog.Proofs.RC` ↦ `Sparkle/Analog/Proofs/RC.lean` (Lake's source root = package root). -/
def moduleSrcPath (mod : String) : String :=
  "/".intercalate (mod.splitOn ".") ++ ".lean"

/-- Parse one fix record written by the sink. -/
def fixOfJson? (j : Json) : Except String Fix := do
  let rule ← j.getObjValAs? String "rule"
  let message ← j.getObjValAs? String "message"
  let range ← j.getObjValAs? Lsp.Range "range"
  let after ← j.getObjValAs? String "after"
  return { rule := Name.mkSimple rule, message, edit := { range, newText := after } }

/-- Read `${dir}/<module>.json` sink files into `Report`s. Each is matched to its current source
file; if the source changed since the build wrote the sink (hash mismatch) it is skipped with a
note (rebuild to refresh). `filter` (module-name prefixes, i.e. lake targets like `Sparkle.Analog`)
limits which modules are reported; empty = all. -/
def readSink (dir : System.FilePath) (filter : List String) : IO (Array Report) := do
  unless ← dir.pathExists do return #[]
  let mut out : Array Report := #[]
  for f in ← System.FilePath.walkDir dir do
    if f.extension != some "json" then continue
    let mod := (f.fileStem).getD ""
    let srcPath := moduleSrcPath mod
    unless filter.isEmpty || filter.any (fun t => mod == t || mod.startsWith (t ++ ".")) do
      continue
    unless ← (System.FilePath.mk srcPath).pathExists do continue
    let src ← IO.FS.readFile srcPath
    let .ok json := Json.parse (← IO.FS.readFile f) | continue
    let stored := (json.getObjValAs? Nat "source").toOption.getD 0
    if hash src != UInt64.ofNat stored then
      IO.eprintln s!"heron-lint: {srcPath} changed since last build — rebuild to refresh"
      continue
    let fixesJson := (json.getObjValAs? (Array Json) "fixes").toOption.getD #[]
    let fixes := fixesJson.filterMap (fun j => (fixOfJson? j).toOption)
    out := out.push { path := srcPath, fileMap := (Parser.mkInputContext src srcPath).fileMap, fixes }
  return out.qsort (·.path < ·.path)

/-! ## Build driver -/

/-- Load the Lake workspace from the current directory (mirrors the `lake` CLI bootstrap) and
return the **root package's** library names — the targets to build/lint by default. -/
def localLibNames : IO (Array String) := do
  let (elan?, lean?, lake?) ← Lake.findInstall?
  let some leanInstall := lean? | throw <| IO.userError "lake: no Lean install found"
  let some lakeInstall := lake? | throw <| IO.userError "lake: no Lake install found"
  let env ← (Lake.Env.compute lakeInstall leanInstall elan? none).toIO
    (fun m => IO.userError s!"lake env: {m}")
  let cfg : Lake.LoadConfig := { lakeEnv := env, wsDir := ← IO.currentDir }
  let some ws ← (Lake.loadWorkspace cfg).toBaseIO
    | throw <| IO.userError "lake: failed to load workspace"
  return ws.root.leanLibs.map (·.name.toString)

/-- Locate Heron's plugin shared library relative to this executable
(`…/.lake/build/bin/heron-lint` → `…/.lake/build/lib/libheron_Heron.so`), overridable with
`HERON_PLUGIN_SO`. -/
def findPluginSo : IO (Option String) := do
  if let some p ← IO.getEnv "HERON_PLUGIN_SO" then return some p
  let cand := (← IO.appDir) / ".." / "lib" / "libheron_Heron.so"
  (some <$> (IO.FS.realPath cand).map (·.toString)) <|> pure none

/-- Run `lake build <targets>` with the Heron plugin + sink enabled. Build stdout is discarded so
it can't corrupt our `--json`/`--apply`; stderr (progress, warnings, errors) is inherited. -/
def runBuild (so fixDir : String) (targets : Array String) : IO Unit := do
  IO.eprintln s!"heron-lint: building {targets.size} target(s) under the Heron plugin…"
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["build"] ++ targets ++ #[s!"-KheronPlugin={so}", "--reconfigure"]
    env := #[("HERON_FIX_DIR", some fixDir)]
    stdout := .null
  }
  let rc ← child.wait
  unless rc == 0 do IO.eprintln s!"heron-lint: lake build exited with code {rc}"

/-! ## Rendering -/

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
    (srcLines : Array String) (fix : Fix) : String := Id.run do
  let s := fm.lspPosToUtf8Pos fix.edit.range.start
  let e := fm.lspPosToUtf8Pos fix.edit.range.end
  let sp := fm.toPosition s
  let ep := fm.toPosition e
  let header := if fix.message.isEmpty then s!"applicable refactor: {fix.rule}" else fix.message
  let gw := (toString ep.line).length
  let gnum (n : Nat) : String := spaces (gw - (toString n).length) ++ toString n
  let bar := pal.blue (spaces gw ++ " |")
  let newText := fix.edit.newText
  let trimmed := newText.trimAscii.toString
  let isDelete := trimmed.isEmpty
  let isSingle := !newText.any (· == '\n')
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
    for rl in newText.splitOn "\n" do
      ls := ls.push (bar ++ "   " ++ pal.green rl)
  ls := ls.push (pal.blue (spaces gw ++ " = ") ++ pal.dim s!"note: heron::{fix.rule}")
  ls := ls.push ""
  return String.intercalate "\n" ls.toList

def fixToJson (file : String) (fm : FileMap) (fix : Fix) : Json :=
  let s := fm.lspPosToUtf8Pos fix.edit.range.start
  let e := fm.lspPosToUtf8Pos fix.edit.range.end
  let pos := fm.toPosition s
  let before := String.Pos.Raw.extract fm.source s e
  Json.mkObj
    [ ("rule", fix.rule.toString)
    , ("message", fix.message)
    , ("file", file)
    , ("line", (pos.line : Nat))
    , ("col", (pos.column + 1 : Nat))
    , ("before", before)
    , ("after", fix.edit.newText) ]

/-! ## CLI -/

structure Cli where
  fix : Bool := false
  apply : Bool := false
  json : Bool := false
  color : Option Bool := none
  noBuild : Bool := false
  paths : List String := []

def parseArgs : List String → Except String Cli
  | [] => .ok {}
  | "--fix" :: r => do pure { (← parseArgs r) with fix := true }
  | "--apply" :: r => do pure { (← parseArgs r) with apply := true }
  | "--json" :: r => do pure { (← parseArgs r) with json := true }
  | "--color" :: r => do pure { (← parseArgs r) with color := some true }
  | "--no-color" :: r => do pure { (← parseArgs r) with color := some false }
  | "--no-build" :: r => do pure { (← parseArgs r) with noBuild := true }
  | arg :: r =>
    if arg.startsWith "-" then .error s!"unknown flag: {arg}"
    else do let c ← parseArgs r; pure { c with paths := arg :: c.paths }

def usage : String :=
  "usage: heron-lint [--fix | --apply | --json] [--no-build] [--color|--no-color] [<lake-target> ...]\n\
   (no targets ⇒ all libraries in the workspace; e.g. `heron-lint Sparkle.Analog IP.RV32`)"

end HeronLint

open HeronLint

def main (args : List String) : IO UInt32 := do
  let cli ← match parseArgs args with
    | .error e => do IO.eprintln s!"heron-lint: {e}\n{usage}"; return 1
    | .ok c => pure c
  let fixDir : System.FilePath := ".lake" / "build" / "heron-fixes"
  -- Targets: explicit lake targets if given, else every library in the workspace's root package.
  let targets ← if cli.paths.isEmpty then localLibNames else pure cli.paths.toArray
  -- Drive the build (unless told to just read the existing sink).
  unless cli.noBuild do
    match ← findPluginSo with
    | none =>
      IO.eprintln "heron-lint: cannot locate libheron_Heron.so (build heron, or set HERON_PLUGIN_SO); \
                   use --no-build to read an existing sink"
      return 1
    | some so => runBuild so fixDir.toString targets
  -- Report: filter to the requested targets (empty = all sink modules).
  let reports ← readSink fixDir cli.paths
  let plain := cli.json || cli.apply
  let useColor ← match cli.color with
    | some b => pure (b && !plain)
    | none => do
      let noColor := (← IO.getEnv "NO_COLOR").isSome
      pure (!plain && !noColor && (← (← IO.getStdout).isTty))
  let pal : Palette := { on := useColor }

  if cli.apply then
    match reports[0]? with
    | some r =>
      unless reports.size == 1 do
        IO.eprintln "heron-lint: --apply needs exactly one matching file; narrow the path or use --fix"
        return 1
      IO.print (applyEdits r.fileMap (r.fixes.map (·.edit)))
      return 0
    | none => IO.eprintln "heron-lint: no matching file"; return 1

  if cli.fix then
    let mut changed := 0
    let mut total := 0
    for r in reports do
      unless r.fixes.isEmpty do
        let patched := applyEdits r.fileMap (r.fixes.map (·.edit))
        if patched != r.fileMap.source then
          IO.FS.writeFile r.path patched
          changed := changed + 1; total := total + r.fixes.size
          IO.eprintln s!"fixed {r.fixes.size} in {r.path}"
    IO.eprintln (pal.warn s!"heron-lint: applied {total} fix(es) across {changed} file(s)")
    return 0

  if cli.json then
    IO.println (Json.arr (reports.flatMap fun r => r.fixes.map (fixToJson r.path r.fileMap))).compress
  else
    let mut total := 0
    for r in reports do
      total := total + r.fixes.size
      let srcLines := r.fileMap.source.splitOn "\n" |>.toArray
      for fix in r.fixes do
        IO.println (renderFix pal r.path r.fileMap srcLines fix)
    IO.eprintln (pal.warn s!"heron-lint: {total} fix(es) across {reports.size} file(s)")
  return 0
