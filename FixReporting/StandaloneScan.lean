import FixReporting.FixReportRendering
import FixReporting.StandaloneScan.SharedEnvironment
import FixReporting.StandaloneScan.PerFile
import FixReporting.StandaloneScan.RuleListing

/-!
# `heron-scan` — self-contained Heron fix reporter

Reports Heron's fixes without touching the build: it imports Heron in its own process and
elaborates the target files. Default engine imports the dependency closure ONCE and detects all
files against it, with an incremental cache + parallelism (`SharedEnv`). `--per-file` uses the
simpler per-file engine (and `-` reads stdin). Requires the scope to be built (oleans exist).

    lake exe heron-scan Sparkle/Analog          # shared-env: import deps once, lint the subtree
    lake exe heron-scan --per-file A.lean B.lean # per-file engine
    cat snippet.lean | lake exe heron-scan -     # stdin
    lake exe heron-scan --json | jq              # machine-readable
    lake exe heron-scan --fix Sparkle/Analog     # rewrite in place
    lake exe heron-scan rules                    # list every check and refactor
-/

open FixReporting

structure Cli where
  fix : Bool := false
  apply : Bool := false
  json : Bool := false
  all : Bool := false
  perFile : Bool := false
  noCache : Bool := false
  noParallel : Bool := false
  color : Option Bool := none
  stdin : Bool := false
  listRules : Bool := false
  requestedChecks : Array Lean.Name := #[]
  paths : List String := []

def parseArgs : List String → Except String Cli
  | [] => .ok {}
  | "--fix" :: r => do pure { (← parseArgs r) with fix := true }
  | "--apply" :: r => do pure { (← parseArgs r) with apply := true }
  | "--json" :: r => do pure { (← parseArgs r) with json := true }
  | "--all" :: r => do pure { (← parseArgs r) with all := true }
  | "--per-file" :: r => do pure { (← parseArgs r) with perFile := true }
  | "--no-cache" :: r => do pure { (← parseArgs r) with noCache := true }
  | "--no-parallel" :: r => do pure { (← parseArgs r) with noParallel := true }
  | "--color" :: r => do pure { (← parseArgs r) with color := some true }
  | "--no-color" :: r => do pure { (← parseArgs r) with color := some false }
  | "-" :: r => do pure { (← parseArgs r) with stdin := true }
  | ["--rule"] => .error "--rule needs a rule name"
  | "--rule" :: rule :: r => do
    let c ← parseArgs r
    pure { c with requestedChecks := #[rule.toName] ++ c.requestedChecks }
  | arg :: r =>
    if arg.startsWith "-" then .error s!"unknown flag: {arg}"
    else do let c ← parseArgs r; pure { c with paths := arg :: c.paths }

def parseCommandLine : List String → Except String Cli
  | "rules" :: rest => do
    let cli ← parseArgs rest
    unless cli.paths.isEmpty && !cli.stdin && cli.requestedChecks.isEmpty do
      throw "`rules` lists every rule and takes no paths or --rule"
    pure { cli with listRules := true }
  | args => parseArgs args

def usage : String :=
  String.intercalate "\n" [
    "usage: heron-scan [--fix|--apply|--json] [--all] [--per-file] [--no-cache] [--no-parallel] \
     [--color|--no-color] [--rule <name>]... <path|-> ...",
    "       heron-scan rules [--json] [--color|--no-color]",
    "(default: import deps once + detect; --per-file: import each file's own env; -: stdin;",
    "--rule: run only the named checks, bypassing the cache; rules: list every check and refactor)"]

private def readStdin : IO String := do (← IO.getStdin).readToEnd

unsafe def main (args : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let cli ← match parseCommandLine args with
    | .error e => do IO.eprintln s!"heron-scan: {e}\n{usage}"; return 1
    | .ok c => pure c
  if cli.listRules then
    let pal : Palette := { on := ← decideColor cli.color cli.json }
    emitRuleCatalog (← Heron.ruleCatalog.get) pal cli.json
    return 0
  let checks ← match selectChecks (← Heron.heronRuleRegistry.get) cli.requestedChecks with
    | .error e => do IO.eprintln s!"heron-scan: {e}"; return 1
    | .ok checks => pure checks
  let files ← expandPaths cli.paths
  if files.isEmpty && !cli.stdin then
    IO.eprintln s!"heron-scan: no input\n{usage}"; return 1
  let mut reports : Array Report := #[]
  if cli.stdin then
    try reports := reports.push (← lintStdin cli.all checks (← readStdin))
    catch e => IO.eprintln s!"heron-scan: <stdin>: {e.toString}"
  unless files.isEmpty do
    if cli.perFile then
      for f in files do
        try reports := reports.push (← lintPerFile cli.all checks f)
        catch e => IO.eprintln s!"heron-scan: {f}: {e.toString}"
    else
      let conc := if cli.noParallel then 1 else 16
      let useCache := !cli.noCache && cli.requestedChecks.isEmpty
      reports := reports ++ (← lintShared cli.all useCache checks conc files)
  let pal : Palette := { on := ← decideColor cli.color (cli.json || cli.apply) }
  emit reports pal cli.json cli.apply cli.fix
