import FixReporting.FixReportRendering
import FixReporting.RulesSubcommand
import FixReporting.CheckSelection
import FixReporting.BoundedParallelMap
import FixReporting.LintSubcommand.BuildFixSink

open Cli FixReporting Lean

namespace FixReporting

def expandLeanFiles (paths : List String) : IO (Array String) := do
  let mut leanFiles : Array String := #[]
  for path in paths do
    if ← System.FilePath.isDir path then
      let entersDirectory := fun (directory : System.FilePath) =>
        pure (match directory.fileName with | some name => !name.startsWith "." | none => true)
      for file in ← System.FilePath.walkDir path entersDirectory do
        if file.extension == some "lean" then leanFiles := leanFiles.push file.toString
    else
      leanFiles := leanFiles.push path
  return leanFiles.qsort (· < ·)

structure ScanInput where
  label : String
  path : Option String
  source : String
  leanArguments : Array String

structure ScanSettings where
  leanExecutable : String
  projectEnvironment : Array (String × Option String)
  pluginPath : String
  ruleOptions : Array String
  includeRefactors : Bool
  memoryMegabytes : Nat
  sinkRoot : System.FilePath

def scanRuleOptions (requestedChecks : Array Name) : Array String :=
  if requestedChecks.isEmpty then #["-Dweak.linter.heron=true"]
  else requestedChecks.map fun checkName => s!"-Dweak.linter.{checkName}=true"

def readScanSink (sinkDirectory : System.FilePath) : IO (Array Heron.FixRecord) := do
  unless ← sinkDirectory.pathExists do return #[]
  let mut fixes := #[]
  for entry in ← sinkDirectory.readDir do
    if entry.path.extension != some "json" then continue
    let .ok sinkJson := Json.parse (← IO.FS.readFile entry.path) | continue
    fixes := fixes ++ (sinkJson.getObjValAs? (Array Heron.FixRecord) "fixes").toOption.getD #[]
  return fixes

def projectLeanEnvironment : IO (Except String (Array (String × Option String))) := do
  let lakeOutput ← IO.Process.output { cmd := "lake", args := #["env"] }
  unless lakeOutput.exitCode == 0 do
    return .error s!"lake env failed:\n{lakeOutput.stderr}"
  return .ok <| (lakeOutput.stdout.splitOn "\n").toArray.filterMap fun line =>
    match line.splitOn "=" with
    | name :: valueParts@(_ :: _) => some (name, some ("=".intercalate valueParts))
    | _ => none

def availableMemoryMegabytes : IO (Option Nat) := do
  let meminfo ← (some <$> IO.FS.readFile "/proc/meminfo") <|> pure none
  let some meminfoText := meminfo | return none
  let availableLine? := (meminfoText.splitOn "\n").find? (·.startsWith "MemAvailable:")
  let some availableLine := availableLine? | return none
  let kilobytes? := ((availableLine.splitOn " ").filter (!·.isEmpty))[1]?.bind (·.toNat?)
  return kilobytes?.map (· / 1024)

def processorCount : IO (Option Nat) := do
  let cpuinfo ← (some <$> IO.FS.readFile "/proc/cpuinfo") <|> pure none
  let some cpuinfoText := cpuinfo | return none
  let processorLines := (cpuinfoText.splitOn "\n").filter (·.startsWith "processor")
  return if processorLines.isEmpty then none else some processorLines.length

def defaultScanJobs : IO Nat := do
  match ← processorCount, ← availableMemoryMegabytes with
  | some processors, some availableMegabytes => return max 1 (min processors (availableMegabytes / 2048))
  | _, _ => return 4

def reportLeanErrors (label : String) (leanOutput : IO.Process.Output) : IO Unit := do
  unless leanOutput.exitCode == 0 do
    IO.eprintln s!"heron scan: {label}: lean exited with code {leanOutput.exitCode}"
    for line in (leanOutput.stdout ++ leanOutput.stderr).splitOn "\n" do
      if line.contains "error" then IO.eprintln s!"  {line}"

def scanInput (settings : ScanSettings) (indexedInput : Nat × ScanInput) : IO Report := do
  let (index, input) := indexedInput
  let sinkDirectory := settings.sinkRoot / toString index
  let refactorEnvironment := if settings.includeRefactors then #[("HERON_FIX_REFACTORS", some "1")] else #[]
  let leanOutput ← IO.Process.output {
    cmd := settings.leanExecutable
    args := #[s!"--plugin={settings.pluginPath}", s!"--memory={settings.memoryMegabytes}"]
      ++ settings.ruleOptions ++ input.leanArguments
    env := settings.projectEnvironment ++ #[("HERON_FIX_DIR", some sinkDirectory.toString)]
      ++ refactorEnvironment }
  reportLeanErrors input.label leanOutput
  return { path := input.path, label := input.label,
           fileMap := (Parser.mkInputContext input.source input.label).fileMap,
           fixes := ← readScanSink sinkDirectory }

def stdinScanInput (sinkRoot : System.FilePath) (source : String) : IO ScanInput := do
  let stdinDirectory := sinkRoot / "stdin"
  IO.FS.createDirAll stdinDirectory
  let stdinFile := stdinDirectory / "Stdin.lean"
  IO.FS.writeFile stdinFile source
  return { label := "<stdin>", path := none, source,
           leanArguments := #[s!"--root={stdinDirectory}", stdinFile.toString] }

end FixReporting

unsafe def runScan (parsed : Parsed) : IO UInt32 := do
  loadRuleInitializers
  let requestedChecks := ((parsed.flag? "rule").map (·.as! (Array String))).getD #[] |>.map (·.toName)
  if let .error message := selectChecks (← Heron.heronRuleRegistry.get) requestedChecks then
    IO.eprintln s!"heron scan: {message}"; return 1
  let inputs := parsed.variableArgsAs! String
  let readsStdin := inputs.contains "-"
  let files ← expandLeanFiles (inputs.filter (· != "-")).toList
  if files.isEmpty && !readsStdin then
    IO.eprintln "heron scan: no input; pass files, directories or - for stdin"; return 1
  let some pluginPath ← ensurePluginSo | do
    IO.eprintln "heron scan: could not build or locate the Heron plugin (set HERON_PLUGIN_SO)"
    return 1
  let projectEnvironment ← match ← projectLeanEnvironment with
    | .ok environment => pure environment
    | .error message => do IO.eprintln s!"heron scan: {message}"; return 1
  let leanExecutable := (projectEnvironment.findSome? fun (name, value) =>
    if name == "LEAN" then value else none).getD "lean"
  let sinkRoot : System.FilePath := ".lake" / "build" / "heron-scan"
  if ← sinkRoot.pathExists then IO.FS.removeDirAll sinkRoot
  IO.FS.createDirAll sinkRoot
  let mut scanInputs ← files.mapM fun (file : String) => do
    return ({ label := file, path := some file, source := ← IO.FS.readFile file,
              leanArguments := #[file] } : ScanInput)
  if readsStdin then
    scanInputs := scanInputs.push (← stdinScanInput sinkRoot (← (← IO.getStdin).readToEnd))
  let settings : ScanSettings :=
    { leanExecutable, projectEnvironment, pluginPath, ruleOptions := scanRuleOptions requestedChecks,
      includeRefactors := parsed.hasFlag "all",
      memoryMegabytes := ((parsed.flag? "memory").map (·.as! Nat)).getD 8192, sinkRoot }
  let jobs ← match parsed.flag? "jobs" with
    | some jobsFlag => pure (jobsFlag.as! Nat)
    | none => defaultScanJobs
  let reports ← boundedParallelMap jobs (scanInputs.zipIdx.map fun (input, index) => (index, input))
    (scanInput settings)
  let json := parsed.hasFlag "json"
  let apply := parsed.hasFlag "apply"
  let pal : Palette := { on := ← decideColor (requestedColor parsed) (json || apply) }
  emit reports pal json apply (parsed.hasFlag "fix")

unsafe def scanCmd : Cmd := `[Cli|
  scan VIA runScan;
  "Run Lean with the Heron plugin on files of a built project and report Heron's fixes, \
   without changes to the project. Run it in the project's root directory."

  FLAGS:
    fix;                     "Rewrite the files in place."
    apply;                   "Print the one input file with every fix applied."
    json;                    "Print the fixes as JSON."
    all;                     "Also run the refactors, which are otherwise only offered as code actions."
    rule : Array String;     "Run only these checks, comma-separated."
    jobs : Nat;              "How many files to check at the same time (default: CPUs, at most one per 2 GB of available memory)."
    memory : Nat;            "Memory limit of each Lean process in megabytes (default 8192)."
    color;                   "Color the output even when stdout is not a terminal."
    "no-color";              "Never color the output."

  ARGS:
    ...inputs : String; "Lean files or directories to scan; - reads one file from stdin."
]
