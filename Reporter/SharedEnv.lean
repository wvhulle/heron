import Lean
import Heron
import Reporter.Render
import Reporter.Frontend

/-! **Shared-environment engine.** Import the dependency closure ONCE, then detect every target file
against that shared imported env — instead of re-importing per file. Incremental cache (by source
hash) + bounded parallelism. Self-contained: needs no lakefile changes and no build, but
re-elaborates (its own cache, separate from Lake's). Requires the scope to be built (oleans exist);
unbuilt modules are skipped. -/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Frontend Lean.Parser
open Heron (FixRecord)

namespace Reporter

/-- A target module: name, source path + contents, and header imports. -/
structure Mod where
  name : Name
  file : String
  src : String
  imports : Array Import
  deriving Inhabited

/-- `Sparkle/Analog/Foo.lean` ↦ `Sparkle.Analog.Foo` (Lake's source root = package root). -/
def modNameOfFile (f : String) : Name :=
  let p := if f.endsWith ".lean" then (f.dropEnd 5).toString else f
  let parts := (p.splitOn "/").filter (fun s => s != "" && s != ".")
  parts.foldl (fun acc s => Name.str acc s) Name.anonymous

def buildMod (name : Name) (file : String) : IO Mod := do
  let src ← IO.FS.readFile file
  let hdr ← Lean.parseImports' src file
  return { name, file, src, imports := hdr.imports }

/-- Expand path args into `.lean` files (directories recursed, `.lake`/dotfiles skipped). -/
def expandPaths (paths : List String) : IO (Array String) := do
  let mut out : Array String := #[]
  for p in paths do
    if ← System.FilePath.isDir p then
      let enter := fun (d : System.FilePath) =>
        pure (match d.fileName with | some n => !n.startsWith "." | none => true)
      for f in ← System.FilePath.walkDir p enter do
        if f.extension == some "lean" then out := out.push f.toString
    else
      out := out.push p
  return out.qsort (· < ·)

/-! ## Incremental cache (this engine's own — separate from Lake's) -/

def cachePath : System.FilePath := ".lake" / "build" / "standalone-fixes-cache.json"

structure CacheEntry where
  hash : UInt64
  fixes : Array FixRecord

def loadCache : IO (Std.HashMap String CacheEntry) := do
  let mut m : Std.HashMap String CacheEntry := ∅
  try
    unless ← cachePath.pathExists do return m
    let .ok json := Json.parse (← IO.FS.readFile cachePath) | return m
    let .ok arr := json.getArr? | return m
    for e in arr do
      let parsed : Except String (String × Nat × Array FixRecord) := do
        return (← e.getObjValAs? String "file", ← e.getObjValAs? Nat "hash",
                ← e.getObjValAs? (Array FixRecord) "fixes")
      if let .ok (file, h, fixes) := parsed then
        m := m.insert file { hash := UInt64.ofNat h, fixes }
  catch _ => pure ()
  return m

def saveCache (m : Std.HashMap String CacheEntry) : IO Unit := do
  try
    if let some d := cachePath.parent then
      if ← d.pathExists then
        let arr := m.toArray.map fun (file, e) =>
          Json.mkObj [("file", file), ("hash", (e.hash.toNat : Nat)), ("fixes", toJson e.fixes)]
        IO.FS.writeFile cachePath (Json.arr arr).compress
  catch _ => pure ()

/-! ## Engine -/

/-- Import the union of the targets' DEPENDENCIES (built oleans) once, then detect each file against
that shared env. Imports only dependency modules (not the targets — so leaf exe roots defining
`main` don't collide); `Init` is excluded (listing it re-runs imported initializers); no dynlibs are
loaded (extern symbols aren't called during elaboration). Per-task stream isolation keeps
`--json`/`--apply` clean under parallelism. -/
def lintMods (all useCache : Bool) (conc : Nat) (mods : Array Mod) : IO (Array Report) := do
  let baseOpts := (Elab.async.set ({} : Options) false).setBool `linter.heron true
  let cache ← if useCache then loadCache else pure ∅
  let mut hits : Array Report := #[]
  let mut misses : Array Mod := #[]
  for m in mods do
    match cache[m.file]? with
    | some e =>
      if e.hash == hash m.src then
        hits := hits.push { path := some m.file, label := m.file,
                            fileMap := (mkInputContext m.src m.file).fileMap, fixes := e.fixes }
      else misses := misses.push m
    | none => misses := misses.push m
  if misses.isEmpty then
    IO.eprintln s!"standalone: {mods.size} file(s) unchanged — all served from cache"
    return hits
  let mut impSet : Std.HashSet Name := ∅
  for m in misses do
    for i in m.imports do
      unless i.module == `Init do impSet := impSet.insert i.module
  let mut importNames : Array Import := #[]
  for n in impSet.toArray do
    let built ← (do let p ← Lean.findOLean n; p.pathExists) <|> pure false
    if built then importNames := importNames.push { module := n }
  IO.eprintln s!"standalone: {hits.size} cached; importing {importNames.size} dependency module(s) to lint {misses.size} file(s) (≤{max 1 conc}-way)…"
  let env ← importModules importNames baseOpts (loadExts := true)
  let lintOne : Mod → IO Report := fun m => do
    try
      let ictx := mkInputContext m.src m.file
      let (_, pstate, _) ← parseHeader ictx
      let fst : Frontend.State :=
        { commandState := Command.mkState env {} baseOpts, parserState := pstate, cmdPos := pstate.pos }
      let (_, (fixes, _)) ← IO.FS.withIsolatedStreams
        (((collectLoop all false #[]).run { inputCtx := ictx }).run fst)
      return { path := some m.file, label := m.file, fileMap := ictx.fileMap, fixes }
    catch e =>
      IO.eprintln s!"standalone: {m.name}: {e.toString}"
      return { path := some m.file, label := m.file, fileMap := (mkInputContext m.src m.file).fileMap, fixes := #[] }
  let fresh ← parMap conc misses lintOne
  if useCache then
    let mut newCache := cache
    for r in fresh do
      if let some path := r.path then
        newCache := newCache.insert path { hash := hash r.fileMap.source, fixes := r.fixes }
    saveCache newCache
  return hits ++ fresh

/-- Lint explicit files/dirs (module names derived from paths). -/
def lintShared (all useCache : Bool) (conc : Nat) (files : Array String) : IO (Array Report) := do
  let mods ← files.mapM fun (f : String) => buildMod (modNameOfFile f) f
  lintMods all useCache conc mods

end Reporter
