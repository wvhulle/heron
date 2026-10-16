import Lean.Data.Lsp

open IO Lean Lsp JsonRpc

structure Cli where
  file : Option String := none
  expected : Array String := #[]
  rejected : Array String := #[]
  expectQuickFix : Bool := false
  server : Option String := none
  serverArgs : Array String := #[]

def parseArgs : List String → Except String Cli
  | [] => .ok {}
  | "--" :: server :: serverArgs => .ok { server := server, serverArgs := serverArgs.toArray }
  | "--expect" :: substring :: rest => do
    let cli ← parseArgs rest
    pure { cli with expected := #[substring] ++ cli.expected }
  | "--reject" :: substring :: rest => do
    let cli ← parseArgs rest
    pure { cli with rejected := #[substring] ++ cli.rejected }
  | "--expect-quick-fix" :: rest => do pure { (← parseArgs rest) with expectQuickFix := true }
  | arg :: rest =>
    if arg.startsWith "-" then .error s!"unknown flag: {arg}"
    else do pure { (← parseArgs rest) with file := arg }

def usage : String :=
  "usage: heron-lsp-probe FILE.lean [--expect SUBSTRING]... [--reject SUBSTRING]... \
   [--expect-quick-fix] -- SERVER [ARGS...]"

def diagnosticCode (diagnostic : Diagnostic) : String :=
  match diagnostic.code? with
  | some (.string code) => code
  | some (.int code) => toString code
  | none => "-"

def printDiagnostic (diagnostic : Diagnostic) : IO Unit :=
  println s!"  {diagnostic.range.start.line}:{diagnostic.range.start.character} \
    [{diagnosticCode diagnostic}] {diagnostic.message.replace "\n" " "}"

def quickFixesFor (uri : DocumentUri) (diagnostic : Diagnostic) : Ipc.IpcM (Array CodeAction) := do
  let params : CodeActionParams :=
    { textDocument := { uri }, range := diagnostic.range, context := { diagnostics := #[diagnostic] } }
  Ipc.writeRequest ⟨2, "textDocument/codeAction", params⟩
  let response ← Ipc.readResponseAs 2 (Array CodeAction)
  return response.result.filter (·.kind? == some "quickfix")

def probe (cli : Cli) (file server : String) : IO UInt32 := do
  let path ← IO.FS.realPath file
  let uri := System.Uri.pathToUri path.toString
  let rootUri := System.Uri.pathToUri (← IO.currentDir).toString
  let text ← IO.FS.readFile path
  Ipc.runWith server cli.serverArgs do
    Ipc.writeRequest ⟨0, "initialize",
      ({ processId? := none, capabilities := {}, rootUri? := some rootUri } : InitializeParams)⟩
    discard <| Ipc.readResponseAs 0 Json
    Ipc.writeNotification ⟨"initialized", InitializedParams.mk⟩
    Ipc.writeNotification ⟨"textDocument/didOpen",
      ({ textDocument := { uri, languageId := "lean", version := 1, text } }
        : DidOpenTextDocumentParams)⟩
    let diagnostics := match ← Ipc.collectDiagnostics 1 uri 1 with
      | some notification => notification.param.diagnostics
      | none => #[]
    println s!"{diagnostics.size} diagnostic(s) for {file}:"
    for diagnostic in diagnostics do printDiagnostic diagnostic
    let mut failures : Array String := #[]
    for substring in cli.expected do
      match diagnostics.find? (·.message.contains substring) with
      | none => failures := failures.push s!"no diagnostic mentions `{substring}`"
      | some diagnostic =>
        if cli.expectQuickFix then
          let quickFixes ← quickFixesFor uri diagnostic
          println s!"{quickFixes.size} quick fix(es) for `{substring}`: \
            {quickFixes.map (·.title) |>.toList}"
          if quickFixes.isEmpty then
            failures := failures.push s!"no quick fix for the diagnostic mentioning `{substring}`"
    for substring in cli.rejected do
      if diagnostics.any (·.message.contains substring) then
        failures := failures.push s!"a diagnostic mentions `{substring}`"
    Ipc.shutdown 3
    discard Ipc.waitForExit
    failures.forM (eprintln s!"heron-lsp-probe: {·}")
    return if failures.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error message => eprintln s!"heron-lsp-probe: {message}\n{usage}"; return 1
  | .ok cli =>
    match cli.file, cli.server with
    | some file, some server => probe cli file server
    | _, _ => eprintln usage; return 1
