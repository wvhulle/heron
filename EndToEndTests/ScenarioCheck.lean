import Lean.Data.Lsp

open IO Lean Lsp JsonRpc

structure ScenarioOptions where
  scenario : String := ""
  expectedFixes : Option System.FilePath := none
  languageServer : Option String := none
  skipEditorProbes : Bool := false

def parseOptions : List String → Except String ScenarioOptions
  | [] => .ok {}
  | "--expected-fixes" :: path :: rest => do pure { (← parseOptions rest) with expectedFixes := path }
  | "--language-server" :: path :: rest => do pure { (← parseOptions rest) with languageServer := path }
  | "--skip-editor-probes" :: rest => do pure { (← parseOptions rest) with skipEditorProbes := true }
  | arg :: rest =>
    if arg.startsWith "-" then .error s!"unknown flag: {arg}"
    else do pure { (← parseOptions rest) with scenario := arg }

def usage : String :=
  "usage: lean --run ScenarioCheck.lean (lakefile-setup | per-file-import) \
   [--expected-fixes FILE] [--language-server PATH] [--skip-editor-probes]"

abbrev CheckM := StateT (Array String) IO

def fail (failure : String) : CheckM Unit := modify (·.push failure)

def runAndPrint (command : String) (args : Array String) : IO IO.Process.Output := do
  let result ← IO.Process.output { cmd := command, args }
  println (result.stdout ++ result.stderr)
  return result

def jobBuiltBy (line : String) : Option String :=
  match line.splitOn " " |>.dropWhile (fun word => !["Built", "Replayed", "Building"].contains word) with
  | _ :: job :: _ => some job
  | _ => none

def heronJobsBuiltTwice (buildLog : String) : List String :=
  let heronJobs := (buildLog.splitOn "\n").filterMap jobBuiltBy |>.filter (·.startsWith "Heron")
  heronJobs.eraseDups.filter fun job => (heronJobs.filter (· == job)).length > 1

def fixSortKey (fix : Json) : String :=
  ["file", "line", "col", "rule", "before"].map (fun field => (fix.getObjValD field).compress)
    |> String.intercalate "\u0000"

def normalizedFixes (fixes : Json) : Except String (Array String) := do
  let entries ← fixes.getArr?
  return (entries.qsort fun a b => fixSortKey a < fixSortKey b).map (·.compress)

def checkLintMatches (expectedFixes : System.FilePath) : CheckM Unit := do
  let lint ← runAndPrint "lake" #["lint", "--", "--json"]
  unless lint.exitCode == 0 do fail "lake lint failed"; return
  let reported := Json.parse lint.stdout >>= normalizedFixes
  let expected := Json.parse (← IO.FS.readFile expectedFixes) >>= normalizedFixes
  match reported, expected with
  | .ok reported, .ok expected =>
    unless reported == expected do
      fail s!"lake lint reported fixes that differ from {expectedFixes}:\n\
        expected:\n{"\n".intercalate expected.toList}\nreported:\n{"\n".intercalate reported.toList}"
  | .error message, _ => fail s!"lake lint did not print a JSON list of fixes: {message}"
  | _, .error message => fail s!"cannot read {expectedFixes}: {message}"

structure EditorProbe where
  file : String
  expected : Array String := #[]
  rejected : Array String := #[]
  expectQuickFix : Bool := false
  server : String
  serverArgs : Array String := #[]

def quickFixesFor (uri : DocumentUri) (diagnostic : Diagnostic) : Ipc.IpcM (Array CodeAction) := do
  let params : CodeActionParams :=
    { textDocument := { uri }, range := diagnostic.range, context := { diagnostics := #[diagnostic] } }
  Ipc.writeRequest ⟨2, "textDocument/codeAction", params⟩
  let response ← Ipc.readResponseAs 2 (Array CodeAction)
  return response.result.filter (·.kind? == some "quickfix")

def runEditorProbe (probe : EditorProbe) : CheckM Unit := do
  let path ← IO.FS.realPath probe.file
  let uri := System.Uri.pathToUri path.toString
  let rootUri := System.Uri.pathToUri (← IO.currentDir).toString
  let text ← IO.FS.readFile path
  let failures ← Ipc.runWith probe.server probe.serverArgs do
    Ipc.writeRequest ⟨0, "initialize",
      ({ processId? := none, capabilities := {}, rootUri? := some rootUri } : InitializeParams)⟩
    discard <| Ipc.readResponseAs 0 Json
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩
    Ipc.writeNotification ⟨"textDocument/didOpen",
      ({ textDocument := { uri, languageId := "lean", version := 1, text } } : DidOpenTextDocumentParams)⟩
    let diagnostics := match ← Ipc.collectDiagnostics 1 uri 1 with
      | some notification => notification.param.diagnostics
      | none => #[]
    println s!"{probe.server}: {diagnostics.size} diagnostic(s) for {probe.file}"
    for diagnostic in diagnostics do
      println s!"  {diagnostic.range.start.line}:{diagnostic.range.start.character} \
        {diagnostic.message.replace "\n" " "}"
    let mut failures : Array String := #[]
    for substring in probe.expected do
      match diagnostics.find? (·.message.contains substring) with
      | none => failures := failures.push s!"{probe.server}: no diagnostic mentions `{substring}`"
      | some diagnostic =>
        if probe.expectQuickFix && (← quickFixesFor uri diagnostic).isEmpty then
          failures := failures.push s!"{probe.server}: no quick fix for the diagnostic mentioning `{substring}`"
    for substring in probe.rejected do
      if diagnostics.any (·.message.contains substring) then
        failures := failures.push s!"{probe.server}: a diagnostic mentions `{substring}`"
    Ipc.shutdown 3
    discard Ipc.waitForExit
    return failures
  modify (· ++ failures)

def checkLakefileSetup (options : ScenarioOptions) : CheckM Unit := do
  let build ← runAndPrint "lake" #["build"]
  let buildLog := build.stdout ++ build.stderr
  let duplicated := heronJobsBuiltTwice buildLog
  unless duplicated.isEmpty do
    fail s!"Lake ran these Heron jobs more than once, so concurrent duplicates can corrupt the build: {duplicated}"
  unless build.exitCode == 0 do fail "cold lake build of the consumer fixture failed"; return
  unless buildLog.contains "warning: Consumer/Basic.lean" do
    fail "lake build did not report Heron diagnostics, so the plugin was not loaded"
  let some expectedFixes := options.expectedFixes | fail "--expected-fixes is required"; return
  checkLintMatches expectedFixes
  if options.skipEditorProbes then return
  runEditorProbe { file := "Consumer/Basic.lean", expected := #["Merge intros", "mut"],
                   expectQuickFix := true, server := "lake", serverArgs := #["serve"] }
  let some languageServer := options.languageServer | fail "--language-server is required"; return
  runEditorProbe { file := "Consumer/Basic.lean", rejected := #["Merge intros"], server := languageServer }

def checkPerFileImport (options : ScenarioOptions) : CheckM Unit := do
  let build ← runAndPrint "lake" #["build"]
  let buildLog := build.stdout ++ build.stderr
  unless build.exitCode == 0 do fail "lake build of the per-file import fixture failed"; return
  unless buildLog.contains "ImportingLibrary/Basic.lean" && buildLog.contains "Merge intros" do
    fail "lake build did not report Heron's hint for the file that imports Heron"
  if options.skipEditorProbes then return
  runEditorProbe { file := "ImportingLibrary/Basic.lean", expected := #["Merge intros"],
                   expectQuickFix := true, server := "lake", serverArgs := #["serve"] }

def main (args : List String) : IO UInt32 := do
  let options ← match parseOptions args with
    | .ok options => pure options
    | .error message => eprintln s!"{message}\n{usage}"; return 1
  let check ← match options.scenario with
    | "lakefile-setup" => pure (checkLakefileSetup options)
    | "per-file-import" => pure (checkPerFileImport options)
    | other => eprintln s!"unknown scenario `{other}`\n{usage}"; return 1
  let ((), failures) ← check.run #[]
  failures.forM (eprintln s!"ScenarioCheck {options.scenario}: {·}")
  return if failures.isEmpty then 0 else 1
