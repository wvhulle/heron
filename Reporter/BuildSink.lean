import Lean
import Lake
import Lake.Load.Workspace
import Heron.Fix
import Reporter.Render

/-! **Build-sink engine (clippy model).** Heron's linter runs during `lake build` and writes each
module's fixes to `$HERON_FIX_DIR/<module>.json` (see `Heron/Check.lean`). This drives that build
(loading Heron as a `lean --plugin` so it lints every module, via the project's `-KheronPlugin`
lakefile wiring) and reads the sink. No elaboration here; Lake's incremental build is the cache. -/

open Lean
open Heron (FixRecord)

namespace Reporter

/-- `Sparkle.Analog.Foo` ↦ `Sparkle/Analog/Foo.lean`. -/
def moduleSrcPath (mod : String) : String := "/".intercalate (mod.splitOn ".") ++ ".lean"

/-- Load the Lake workspace from cwd and return the **root package's** library names — the default
targets to build/lint. -/
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
(`…/.lake/build/bin/<exe>` → `…/.lake/build/lib/libheron_Heron.so`), overridable with
`HERON_PLUGIN_SO`. -/
def findPluginSo : IO (Option String) := do
  if let some p ← IO.getEnv "HERON_PLUGIN_SO" then return some p
  let cand := (← IO.appDir) / ".." / "lib" / "libheron_Heron.so"
  (some <$> (IO.FS.realPath cand).map (·.toString)) <|> pure none

/-- Build Heron's plugin shared library (`heron/Heron:shared`) in the current workspace, so the
plugin is provided out of the box — the user never has to locate or pre-build the `.so`. The target
is package-qualified (`heron/Heron`) so it resolves whether Heron is the root package or a
dependency. Build output is forwarded to stderr; failures are non-fatal (we still try to locate a
pre-existing `.so`). -/
def buildPluginSo : IO Unit := do
  IO.eprintln "heron: building the Heron plugin (heron/Heron:shared)…"
  let child ← IO.Process.spawn {
    cmd := "lake", args := #["build", "heron/Heron:shared"], stdout := .piped }
  let out ← child.stdout.readToEnd
  let rc ← child.wait
  unless out.isEmpty do IO.eprint out
  unless rc == 0 do
    IO.eprintln s!"heron: building the plugin exited with code {rc}; will try an existing .so"

/-- Ensure the plugin `.so` exists (building it if necessary) and return its path. -/
def ensurePluginSo : IO (Option String) := do
  if let some p ← findPluginSo then return some p
  buildPluginSo
  findPluginSo

/-- Run `lake build <targets>` with the Heron plugin + sink enabled. Build stdout is forwarded to
our stderr (so progress/errors stay visible) keeping our stdout clean for `--json`/`--apply`. A
non-zero exit (some target failed) is reported but non-fatal. -/
def runBuild (so fixDir : String) (targets : Array String) : IO Unit := do
  IO.eprintln s!"heron: building {targets.size} target(s) under the Heron plugin…"
  let child ← IO.Process.spawn {
    cmd := "lake"
    args := #["build"] ++ targets ++ #[s!"-KheronPlugin={so}", "--reconfigure"]
    env := #[("HERON_FIX_DIR", some fixDir)]
    stdout := .piped
  }
  let out ← child.stdout.readToEnd
  let rc ← child.wait
  unless out.isEmpty do IO.eprint out
  unless rc == 0 do
    IO.eprintln s!"heron: lake build exited with code {rc} — some target failed; \
                  reporting fixes for the targets that did build"

/-- Read `${dir}/<module>.json` sink files into `Report`s. Each is matched to its current source;
a source-hash mismatch (changed since the build) is skipped with a note. `filter` (module-name
prefixes / lake targets like `Sparkle.Analog`) limits which are reported; empty = all. -/
def readSink (dir : System.FilePath) (filter : List String) : IO (Array Report) := do
  unless ← dir.pathExists do return #[]
  let mut out : Array Report := #[]
  for f in ← System.FilePath.walkDir dir do
    if f.extension != some "json" then continue
    let mod := (f.fileStem).getD ""
    let srcPath := moduleSrcPath mod
    unless filter.isEmpty || filter.any (fun t => mod == t || mod.startsWith (t ++ ".")) do continue
    unless ← (System.FilePath.mk srcPath).pathExists do continue
    let src ← IO.FS.readFile srcPath
    let .ok json := Json.parse (← IO.FS.readFile f) | continue
    let stored := (json.getObjValAs? Nat "source").toOption.getD 0
    if hash src != UInt64.ofNat stored then
      IO.eprintln s!"heron: {srcPath} changed since last build — rebuild to refresh"
      continue
    let fixes := (json.getObjValAs? (Array FixRecord) "fixes").toOption.getD #[]
    out := out.push { path := some srcPath, label := srcPath, fileMap := (Lean.Parser.mkInputContext src srcPath).fileMap, fixes }
  return out.qsort (fun a b => a.label < b.label)

end Reporter
