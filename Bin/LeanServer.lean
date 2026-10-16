import Reporter.PluginSo
import Lean.Data.Lsp.Communication
import Std.Data.HashMap

open System Reporter Lean JsonRpc

def heronRepository : String := "https://github.com/wvhulle/heron"

def fail (message : String) : IO α :=
  throw <| IO.userError s!"heron-language-server: {message}"

def parseLeanVersion (versionOutput : String) : Option String :=
  match versionOutput.splitOn "(version " with
  | [_, afterMarker] => (afterMarker.splitOn ",").head?
  | _ => none

def projectLeanVersion : IO String := do
  let out ← IO.Process.output { cmd := "lean", args := #["--version"] }
  unless out.exitCode == 0 do
    fail s!"`lean --version` failed in {← IO.currentDir}:\n{out.stderr}"
  match parseLeanVersion out.stdout with
  | some version => pure version
  | none => fail s!"cannot read a version from `lean --version`: {out.stdout}"

def siblingPluginFor (version : String) : IO (Option String) := do
  if version != Lean.versionString then return none
  findPluginSo

def cacheRoot : IO FilePath := do
  if let some dir ← IO.getEnv "HERON_CACHE_DIR" then return dir
  if let some dir ← IO.getEnv "XDG_CACHE_HOME" then return FilePath.mk dir / "heron"
  match ← IO.getEnv "HOME" with
  | some home => return FilePath.mk home / ".cache" / "heron"
  | none => fail "neither HERON_CACHE_DIR, XDG_CACHE_HOME nor HOME is set"

def builtPlugin (checkout : FilePath) : FilePath :=
  checkout / ".lake" / "build" / "lib" / pluginSoFileName

def environmentOfOtherToolchain : Array (String × Option String) :=
  #["ELAN_TOOLCHAIN", "LAKE", "LEAN", "LEAN_SYSROOT", "LEAN_PATH", "LEAN_SRC_PATH"].map (·, none)

def runReportingToStderr (cmd : String) (args : Array String) (cwd : Option FilePath := none) :
    IO Bool := do
  let out ← IO.Process.output
    { cmd, args, cwd, env := environmentOfOtherToolchain }
  IO.eprint out.stdout
  IO.eprint out.stderr
  return out.exitCode == 0

def checkoutTargetsVersion (checkout : FilePath) (version : String) : IO Bool := do
  let toolchain ← IO.FS.readFile (checkout / "lean-toolchain") <|> pure ""
  return toolchain.trimAscii.toString.endsWith s!":v{version}"

def cloneBranchFor (version : String) (checkout : FilePath) : IO Bool := do
  for branch in [s!"lean/v{version}", "main"] do
    if ← checkout.pathExists then IO.FS.removeDirAll checkout
    IO.eprintln s!"heron-language-server: fetching Heron branch {branch} for Lean {version}"
    let cloned ← runReportingToStderr "git"
      #["clone", "--quiet", "--depth", "1", "--branch", branch, heronRepository, checkout.toString]
    if cloned && (← checkoutTargetsVersion checkout version) then return true
  if ← checkout.pathExists then IO.FS.removeDirAll checkout
  return false

def buildCachedPlugin (version : String) (checkout : FilePath) : IO (Option String) := do
  unless ← checkoutTargetsVersion checkout version do
    unless ← cloneBranchFor version checkout do return none
  IO.eprintln s!"heron-language-server: building the Heron plugin for Lean {version} in {checkout}"
  unless ← runReportingToStderr "lake" #["build", "Heron:shared"] checkout do return none
  let plugin := builtPlugin checkout
  return if ← plugin.pathExists then some plugin.toString else none

def cachedPluginFor (version : String) : IO (Option String) := do
  let root ← cacheRoot
  IO.FS.createDirAll root
  let checkout := root / version
  if ← (builtPlugin checkout).pathExists then return some (builtPlugin checkout).toString
  let lock ← IO.FS.Handle.mk (root / s!"{version}.lock") .write
  lock.lock
  try
    if ← (builtPlugin checkout).pathExists then return some (builtPlugin checkout).toString
    buildCachedPlugin version checkout
  finally
    lock.unlock

def resolvePlugin (version : String) : IO String := do
  if let some plugin ← siblingPluginFor version then return plugin
  if let some plugin ← cachedPluginFor version then return plugin
  fail s!"no Heron plugin for Lean {version}. Heron has no branch lean/v{version} at \
    {heronRepository}, or building it failed (see above). Cache: {← cacheRoot}"

def lakefileLoadsHeronPlugin : IO Bool :=
  ["lakefile.lean", "lakefile.toml"].anyM fun (lakefile : String) => do
    let config ← IO.FS.readFile lakefile <|> pure ""
    return config.contains "@heron/plugin"

def pluginForProject : IO (Option String) := do
  if ← lakefileLoadsHeronPlugin then
    IO.eprintln "heron-language-server: the lakefile already loads @heron/plugin, so the Lean server \
      shows Heron's hints itself"
    return none
  try
    return some (← resolvePlugin (← projectLeanVersion))
  catch e =>
    IO.eprintln e
    return none

def isHeronName (json : Json) : Bool :=
  match json.getStr? with
  | .ok name => name.startsWith "heron."
  | .error _ => false

def isHeronDiagnostic (diagnostic : Json) : Bool :=
  isHeronName (diagnostic.getObjValD "code")

def isHeronCodeAction (action : Json) : Bool :=
  isHeronName ((action.getObjValD "data").getObjValD "providerName")

def keepArrayElements (keep : Json → Bool) (json : Json) : Json :=
  match json.getArr? with
  | .ok elements => Json.arr (elements.filter keep)
  | .error _ => json

def capabilitiesOfHeron (initializeResult : Json) : Json :=
  let capabilities := initializeResult.getObjValD "capabilities"
  let kept := ["positionEncoding", "textDocumentSync", "codeActionProvider"].filterMap fun key =>
    (capabilities.getObjVal? key).toOption.map (key, ·)
  initializeResult.setObjVal! "capabilities" (Json.mkObj kept)

def restrictParams (restrict : Json → Json) (params : Json.Structured) : Json.Structured :=
  match fromJson? (restrict (toJson params)) with
  | .ok restricted => restricted
  | .error _ => params

def diagnosticsOfHeron (params : Json) : Json :=
  params.setObjVal! "diagnostics" (keepArrayElements isHeronDiagnostic (params.getObjValD "diagnostics"))

abbrev PendingRequests := IO.Ref (Std.HashMap RequestID String)

def restrictToHeron (pending : PendingRequests) : Message → IO Message
  | .response id result => do
    let method ← pending.modifyGet fun requests => (requests.get? id, requests.erase id)
    return .response id <| match method with
      | some "initialize" => capabilitiesOfHeron result
      | some "textDocument/codeAction" => keepArrayElements isHeronCodeAction result
      | _ => result
  | .notification "textDocument/publishDiagnostics" (some params) =>
    return .notification "textDocument/publishDiagnostics" (restrictParams diagnosticsOfHeron params)
  | message => return message

partial def relayClientToServer (pending : PendingRequests) (client server : IO.FS.Stream) :
    IO Unit := do
  let message ← client.readLspMessage
  if let .request id method _ := message then pending.modify (·.insert id method)
  server.writeLspMessage message
  unless message matches .notification "exit" _ do relayClientToServer pending client server

partial def relayServerToClient (pending : PendingRequests) (server client : IO.FS.Stream) :
    IO Unit := do
  client.writeLspMessage (← restrictToHeron pending (← server.readLspMessage))
  relayServerToClient pending server client

def serveHeronOnly (plugin : String) (serveArgs : List String) : IO UInt32 := do
  let lake ← IO.Process.spawn {
    cmd := "lake"
    args := #["serve", "--", s!"--plugin={plugin}", "-Dweak.linter.heron=true"] ++ serveArgs
    stdin := .piped
    stdout := .piped
  }
  let (lakeStdin, lake) ← lake.takeStdin
  let pending ← IO.mkRef {}
  let client ← IO.getStdin
  let fromClient ← IO.asTask (prio := .dedicated)
    (relayClientToServer pending client (IO.FS.Stream.ofHandle lakeStdin))
  try relayServerToClient pending (IO.FS.Stream.ofHandle lake.stdout) (← IO.getStdout)
  catch _ => pure ()
  IO.cancel fromClient
  lake.wait

partial def serveNothing (client output : IO.FS.Stream) : IO UInt32 := do
  match ← client.readLspMessage with
  | .request id "initialize" _ =>
    output.writeLspMessage (.response id (Json.mkObj [("capabilities", Json.mkObj [])]))
    serveNothing client output
  | .request id _ _ =>
    output.writeLspMessage (.response id Json.null)
    serveNothing client output
  | .notification "exit" _ => return 0
  | _ => serveNothing client output

def main (serveArgs : List String) : IO UInt32 := do
  match ← pluginForProject with
  | some plugin => serveHeronOnly plugin serveArgs
  | none =>
    IO.eprintln "heron-language-server: serving no Heron hints for this project"
    serveNothing (← IO.getStdin) (← IO.getStdout)
