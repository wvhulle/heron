import FixReporting.FixReportRendering
import FixReporting.RulesSubcommand
import FixReporting.ScanSubcommand.SharedEnvironment
import FixReporting.ScanSubcommand.PerFile

/-!
# `heron scan` — self-contained Heron fix reporter

Reports Heron's fixes without touching the build: it imports Heron in its own process and
elaborates the target files. Default engine imports the dependency closure ONCE and detects all
files against it, with an incremental cache + parallelism (`SharedEnv`). `--per-file` uses the
simpler per-file engine (and `-` reads stdin). Requires the scope to be built (oleans exist).

    heron scan Sparkle/Analog          # shared-env: import deps once, lint the subtree
    heron scan --per-file A.lean B.lean # per-file engine
    cat snippet.lean | heron scan -     # stdin
    heron scan --json Sparkle | jq      # machine-readable
    heron scan --fix Sparkle/Analog     # rewrite in place
-/

open Cli FixReporting

private def readStdin : IO String := do (← IO.getStdin).readToEnd

def lakeProjectSearchPath : IO System.SearchPath := do
  if (← IO.getEnv "LEAN_PATH").isSome then return ∅
  let out ← IO.Process.output { cmd := "lake", args := #["env", "printenv", "LEAN_PATH"] }
  if out.exitCode != 0 then return ∅
  return System.SearchPath.parse out.stdout.trimAscii.toString

unsafe def runScan (parsed : Parsed) : IO UInt32 := do
  loadRuleInitializers (← lakeProjectSearchPath)
  let requestedChecks := ((parsed.flag? "rule").map (·.as! (Array String))).getD #[] |>.map (·.toName)
  let checks ← match selectChecks (← Heron.heronRuleRegistry.get) requestedChecks with
    | .error e => do IO.eprintln s!"heron scan: {e}"; return 1
    | .ok checks => pure checks
  let inputs := parsed.variableArgsAs! String
  let readsStdin := inputs.contains "-"
  let files ← expandPaths (inputs.filter (· != "-")).toList
  if files.isEmpty && !readsStdin then
    IO.eprintln "heron scan: no input; pass files, directories or - for stdin"; return 1
  let all := parsed.hasFlag "all"
  let mut reports : Array Report := #[]
  if readsStdin then
    try reports := reports.push (← lintStdin all checks (← readStdin))
    catch e => IO.eprintln s!"heron scan: <stdin>: {e.toString}"
  unless files.isEmpty do
    if parsed.hasFlag "per-file" then
      for f in files do
        try reports := reports.push (← lintPerFile all checks f)
        catch e => IO.eprintln s!"heron scan: {f}: {e.toString}"
    else
      let conc := if parsed.hasFlag "no-parallel" then 1 else 16
      let useCache := !parsed.hasFlag "no-cache" && requestedChecks.isEmpty
      reports := reports ++ (← lintShared all useCache checks conc files)
  let json := parsed.hasFlag "json"
  let apply := parsed.hasFlag "apply"
  let pal : Palette := { on := ← decideColor (requestedColor parsed) (json || apply) }
  emit reports pal json apply (parsed.hasFlag "fix")

unsafe def scanCmd : Cmd := `[Cli|
  scan VIA runScan;
  "Elaborate files of a built project in this process and report Heron's fixes, \
   without changes to the project. Run it in the project's root directory."

  FLAGS:
    fix;                     "Rewrite the files in place."
    apply;                   "Print the one input file with every fix applied."
    json;                    "Print the fixes as JSON."
    all;                     "Also run the refactors, which are otherwise only offered as code actions."
    "per-file";              "Import each file's own environment instead of the shared dependency closure."
    "no-cache";              "Ignore and do not update the cache of earlier results."
    "no-parallel";           "Elaborate one file at a time."
    rule : Array String;     "Run only these checks, comma-separated; bypasses the cache."
    color;                   "Color the output even when stdout is not a terminal."
    "no-color";              "Never color the output."

  ARGS:
    ...inputs : String; "Lean files or directories to scan; - reads one file from stdin."
]
