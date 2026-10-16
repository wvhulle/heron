import Reporter.PluginSo

open System Reporter

def heronRepository : String := "https://github.com/wvhulle/heron"

def fail (message : String) : IO α :=
  throw <| IO.userError s!"heron-lean-server: {message}"

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
    IO.eprintln s!"heron-lean-server: fetching Heron branch {branch} for Lean {version}"
    let cloned ← runReportingToStderr "git"
      #["clone", "--quiet", "--depth", "1", "--branch", branch, heronRepository, checkout.toString]
    if cloned && (← checkoutTargetsVersion checkout version) then return true
  if ← checkout.pathExists then IO.FS.removeDirAll checkout
  return false

def buildCachedPlugin (version : String) (checkout : FilePath) : IO (Option String) := do
  unless ← checkoutTargetsVersion checkout version do
    unless ← cloneBranchFor version checkout do return none
  IO.eprintln s!"heron-lean-server: building the Heron plugin for Lean {version} in {checkout}"
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

def heronServeArgs : IO (Array String) := do
  if ← lakefileLoadsHeronPlugin then return #[]
  let plugin ← resolvePlugin (← projectLeanVersion)
  return #[s!"--plugin={plugin}", "-Dweak.linter.heron=true"]

def main (serveArgs : List String) : IO UInt32 := do
  try
    let server ← IO.Process.spawn {
      cmd := "lake"
      args := #["serve", "--"] ++ (← heronServeArgs) ++ serveArgs
    }
    server.wait
  catch e =>
    IO.eprintln e
    return 1
