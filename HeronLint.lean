import Lean
import Heron

/-!
# `heron-lint` — headless fix reporter

Drives the Lean frontend over Lean source, runs Heron's checks against every
top-level command, and reports the suggested fixes with `cargo clippy`-style
diagnostics (source context, carets, and the proposed replacement).

Heron otherwise only surfaces its replacements as LSP code actions in an editor;
the plain `lake build` diagnostic carries the headline but not the fix text. This
binary exposes the same `Replacement → TextEdit` path the LSP provider and the
`#assertCheck` test harness use, so fixes can be inspected — and, with `--fix`,
applied and rebuilt — headlessly.

Inputs may be files, directories (recursed for `*.lean`, skipping `.lake` and
dotfiles — point at a library's source dir to lint a whole lake target), or `-`
for stdin. Run under the target project's environment so imports resolve:

    lake env heron-lint Sparkle/Analog                 # lint a whole subtree
    lake env heron-lint A.lean B.lean                  # several files
    lake env heron-lint --fix Sparkle                  # rewrite files in place
    lake env heron-lint --apply A.lean > A.fixed.lean  # patched source to stdout
    lake env heron-lint --json Sparkle | jq            # machine-readable findings
    cat snippet.lean | lake env heron-lint -           # stdin
-/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Frontend Lean.Parser

namespace HeronLint

/-- A single suggested edit: which rule produced it, the rule's headline, and the
LSP text edit (source range + replacement text). -/
structure Fix where
  rule : Name
  message : String
  edit : Lsp.TextEdit

/-- Elaborate a command while swallowing diagnostics, so rules that consult info
trees fire. Mirrors `Heron.Assert`'s elaboration helper. -/
meta def elabCommandSilently (cmd : Syntax) : CommandElabM Unit :=
  withScope (fun scope => { scope with opts := Elab.async.set scope.opts false }) do
    withReader ({ · with snap? := none }) do
      try elabCommand cmd catch _ => pure ()

/-- Run Heron's rules against `cmd`, returning a `Fix` per suggested replacement.

**Checks** (the rules the linter actually emits) are always collected from
`heronRuleRegistry`, filtered by the same `isEnabled` gate the master linter uses,
so the output reflects what `lake build` would warn about — and each carries its
rule headline. When `all` is `true`, the manual-only **refactors** (`inline`,
`flipIf`, …) that the linter never suggests on its own are additionally collected
from `testRunnerRegistry`. -/
meta def collectFixes (all : Bool) (cmd : Syntax) : CommandElabM (Array Fix) := do
  let saved := (← get).messages
  let fileMap ← getFileMap
  let result ← withoutModifyingEnv do
    elabCommandSilently cmd
    let entries ← Heron.heronRuleRegistry.get
    let opts ← getOptions
    let checkNames := entries.map (·.name)
    let mut acc : Array Fix := #[]
    for entry in entries do
      if entry.isEnabled opts then
        let detected ← entry.findActions cmd
        for (msg, repls) in detected do
          let title := (← msg.toString).trimAscii.toString
          for repl in repls do
            let edit? ← liftCoreM (repl.toTextEdit fileMap)
            if let some edit := edit? then
              acc := acc.push { rule := entry.name, message := title, edit }
    if all then
      let runners ← Heron.testRunnerRegistry.get
      for (name, runner) in runners.toList do
        unless checkNames.contains name do
          let res ← runner cmd
          for edit in res.edits do
            acc := acc.push { rule := name, message := "", edit }
    pure acc
  modify fun s => { s with messages := saved }
  return result

/-- Apply non-overlapping LSP `TextEdit`s to a source string. Edits are sorted by
range start descending and applied back-to-front so earlier byte offsets stay
valid (LSP ranges refer to the original document). Matches `Heron.Assert.applyEdits`. -/
def applyEdits (text : FileMap) (edits : Array Lsp.TextEdit) : String :=
  let sorted := edits.qsort fun a b =>
    text.lspPosToUtf8Pos b.range.start < text.lspPosToUtf8Pos a.range.start
  sorted.foldl (init := text.source) fun src edit =>
    let startPos := text.lspPosToUtf8Pos edit.range.start
    let endPos := text.lspPosToUtf8Pos edit.range.end
    let pre := String.Pos.Raw.extract src 0 startPos
    let post := String.Pos.Raw.extract src endPos src.rawEndPos
    pre ++ edit.newText ++ post

/-- Walk every top-level command, gathering a `Fix` for each suggested edit.
Detection runs in the command's *pre*-state (before its real elaboration is
committed), matching how the live linter observes each command; the real
elaboration that follows keeps `namespace`/`open`/`variable` scope correct for
subsequent commands. -/
partial def collectLoop (all : Bool) (acc : Array Fix) : FrontendM (Array Fix) := do
  updateCmdPos
  let cmdState ← getCommandState
  let ictx ← getInputContext
  let pstate ← getParserState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts,
                 currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmd, ps, messages) := parseCommand ictx pmctx pstate cmdState.messages
  setParserState ps
  setMessages messages
  let found ← runCommandElabM (collectFixes all cmd)
  elabCommandAtFrontend cmd
  let acc := acc ++ found
  if isTerminalCommand cmd then return acc else collectLoop all acc

/-- Elaborate `source` (labelled `label` for diagnostics) headlessly and collect
all suggested fixes, in source order. Throws if the imports fail to load. -/
def lintSource (all : Bool) (label : String) (source : String) : IO (FileMap × Array Fix) := do
  let inputCtx := mkInputContext source label
  let (header, parserState, msgs) ← parseHeader inputCtx
  -- Deterministic, synchronous elaboration so fix collection is stable. Seed
  -- `linter.heron := true` to match how Sparkle enables every rule repo-wide (its
  -- `weak.linter.heron` lakefile option); in-file `set_option`s still apply.
  let opts := (Elab.async.set ({} : Options) false).setBool `linter.heron true
  -- The main-module name is irrelevant when linting an external file; deriving it
  -- via `moduleNameOfFileName` would wrongly require the file to live under the cwd.
  let (env, msgs) ← processHeader header opts msgs inputCtx
  if msgs.hasErrors then
    for m in msgs.toList do IO.eprintln (← m.toString)
    throw <| IO.userError s!"failed to load imports of {label}"
  let frontendState : Frontend.State :=
    { commandState := Command.mkState env msgs opts
      parserState
      cmdPos := parserState.pos }
  let (collected, _) ← ((collectLoop all #[]).run { inputCtx }).run frontendState
  return (inputCtx.fileMap, collected)

/-! ## Rendering -/

/-- ANSI colouring, gated on whether output is a terminal. -/
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

/-! ## Input resolution -/

/-- A unit of work: source text plus how to label and (optionally) rewrite it. -/
structure Input where
  /-- Filesystem path, or `none` for stdin (which `--fix` refuses). -/
  path : Option String
  label : String
  source : String
  deriving Inhabited

/-- Expand CLI path arguments into concrete `.lean` files. Directories are walked
recursively; `.lake`, `.git`, and other dotfiles are skipped. -/
def expandPaths (paths : List String) : IO (Array String) := do
  let mut out : Array String := #[]
  for p in paths do
    if ← System.FilePath.isDir p then
      let enter := fun (d : System.FilePath) =>
        pure (match d.fileName with | some n => !n.startsWith "." | none => true)
      let files ← System.FilePath.walkDir p enter
      for f in files do
        if f.extension == some "lean" then out := out.push f.toString
    else
      out := out.push p
  return out.qsort (· < ·)

/-! ## CLI -/

structure Cli where
  fix : Bool := false
  apply : Bool := false
  json : Bool := false
  all : Bool := false
  color : Option Bool := none
  paths : List String := []
  stdin : Bool := false

def parseArgs : List String → Except String Cli
  | [] => .ok {}
  | "--fix" :: r => do pure { (← parseArgs r) with fix := true }
  | "--apply" :: r => do pure { (← parseArgs r) with apply := true }
  | "--json" :: r => do pure { (← parseArgs r) with json := true }
  | "--all" :: r => do pure { (← parseArgs r) with all := true }
  | "--color" :: r => do pure { (← parseArgs r) with color := some true }
  | "--no-color" :: r => do pure { (← parseArgs r) with color := some false }
  | "-" :: r => do pure { (← parseArgs r) with stdin := true }
  | arg :: r =>
    if arg.startsWith "-" then .error s!"unknown flag: {arg}"
    else do let c ← parseArgs r; pure { c with paths := arg :: c.paths }

def usage : String :=
  "usage: heron-lint [--fix | --apply | --json] [--all] [--color|--no-color] <path|-> ..."

end HeronLint

open HeronLint

private def readStdin : IO String := do (← IO.getStdin).readToEnd

unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let cli ← match parseArgs args with
    | .error e => do IO.eprintln s!"heron-lint: {e}\n{usage}"; return 1
    | .ok c => pure c
  -- Resolve inputs.
  let mut inputs : Array Input := #[]
  if cli.stdin then
    inputs := inputs.push { path := none, label := "<stdin>", source := ← readStdin }
  for f in ← expandPaths cli.paths do
    inputs := inputs.push { path := some f, label := f, source := ← IO.FS.readFile f }
  if inputs.isEmpty then
    IO.eprintln s!"heron-lint: no input\n{usage}"
    return 1
  -- Colour: forced flags win; otherwise on for a terminal unless NO_COLOR is set.
  let plain := cli.json || cli.apply
  let useColor ← match cli.color with
    | some b => pure (b && !plain)
    | none => do
      let noColor := (← IO.getEnv "NO_COLOR").isSome
      pure (!plain && !noColor && (← (← IO.getStdout).isTty))
  let pal : Palette := { on := useColor }

  -- `--apply`: patched source of a single input to stdout.
  if cli.apply then
    unless inputs.size == 1 do
      IO.eprintln "heron-lint: --apply takes exactly one input; use --fix for multiple"
      return 1
    let inp := inputs[0]!
    let (fm, fixes) ← lintSource cli.all inp.label inp.source
    IO.print (applyEdits fm (fixes.map (·.edit)))
    return 0

  -- `--fix`: rewrite files in place.
  if cli.fix then
    if cli.stdin then IO.eprintln "heron-lint: --fix cannot rewrite stdin"; return 1
    let mut changed := 0
    let mut total := 0
    for inp in inputs do
      let some path := inp.path | continue
      try
        let (fm, fixes) ← lintSource cli.all inp.label inp.source
        unless fixes.isEmpty do
          let patched := applyEdits fm (fixes.map (·.edit))
          if patched != inp.source then
            IO.FS.writeFile path patched
            changed := changed + 1
            total := total + fixes.size
            IO.eprintln s!"fixed {fixes.size} in {path}"
      catch ex => IO.eprintln s!"heron-lint: {path}: {ex.toString}"
    IO.eprintln (pal.warn s!"heron-lint: applied {total} fix(es) across {changed} file(s)")
    return 0

  -- Default / `--json`: report findings.
  let mut allJson : Array Json := #[]
  let mut total := 0
  let mut failed := 0
  let n := inputs.size
  for i in [0:n] do
    let inp := inputs[i]!
    if n > 1 && !cli.json && useColor then
      IO.eprint s!"\r{pal.dim s!"[{i + 1}/{n}] {inp.label}"}\x1b[K"
    try
      let (fm, fixes) ← lintSource cli.all inp.label inp.source
      total := total + fixes.size
      if cli.json then
        allJson := allJson ++ fixes.map (fixToJson inp.label fm)
      else
        let srcLines := fm.source.splitOn "\n" |>.toArray
        for fix in fixes do
          IO.println (renderFix pal inp.label fm srcLines fix)
    catch ex =>
      failed := failed + 1
      IO.eprintln s!"heron-lint: {inp.label}: {ex.toString}"
  if n > 1 && !cli.json && useColor then IO.eprint "\r\x1b[K"
  if cli.json then
    IO.println (Json.arr allJson).compress
  else
    let suffix := if failed == 0 then "" else s!", {failed} file(s) failed to load"
    IO.eprintln (pal.warn s!"heron-lint: {total} fix(es) across {n} file(s){suffix}")
  return 0
