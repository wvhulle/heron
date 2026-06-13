import Cli.Render
import Cli.BuildSink

/-!
# `heron` — build-integrated Heron fix reporter (clippy model)

Drives `lake build` with Heron loaded as a `lean --plugin` so the linter runs on every module and
writes its fixes to a sink during the build, then reads + renders them. Lake's incremental build is
the cache — no re-elaboration, no cache of our own. Requires the project's lakefile to honour
`-KheronPlugin` (see Sparkle's `lakefile.lean`).

    lake env heron                  # build all libraries + report all fixes
    lake env heron Sparkle.Analog   # restrict build + report to lake targets
    lake env heron --json | jq
    lake env heron --fix            # rewrite files in place
    lake env heron --no-build       # read the existing sink only
-/

open Cli

structure Cli where
  fix : Bool := false
  apply : Bool := false
  json : Bool := false
  color : Option Bool := none
  noBuild : Bool := false
  paths : List String := []

def parseArgs : List String → Except String Cli
  | [] => .ok {}
  | "--fix" :: r => do pure { (← parseArgs r) with fix := true }
  | "--apply" :: r => do pure { (← parseArgs r) with apply := true }
  | "--json" :: r => do pure { (← parseArgs r) with json := true }
  | "--color" :: r => do pure { (← parseArgs r) with color := some true }
  | "--no-color" :: r => do pure { (← parseArgs r) with color := some false }
  | "--no-build" :: r => do pure { (← parseArgs r) with noBuild := true }
  | arg :: r =>
    if arg.startsWith "-" then .error s!"unknown flag: {arg}"
    else do let c ← parseArgs r; pure { c with paths := arg :: c.paths }

def usage : String :=
  "usage: heron [--fix | --apply | --json] [--no-build] [--color|--no-color] [<lake-target> ...]\n\
   (no targets ⇒ all libraries in the workspace; e.g. `heron Sparkle.Analog IP.RV32`)"

def main (args : List String) : IO UInt32 := do
  let cli ← match parseArgs args with
    | .error e => do IO.eprintln s!"heron: {e}\n{usage}"; return 1
    | .ok c => pure c
  let fixDir : System.FilePath := ".lake" / "build" / "heron-fixes"
  let targets ← if cli.paths.isEmpty then localLibNames else pure cli.paths.toArray
  unless cli.noBuild do
    -- Ensure the plugin `.so` exists so the consumer's always-on `--plugin` wiring resolves.
    match ← ensurePluginSo with
    | none =>
      IO.eprintln "heron: could not build or locate libheron_Heron.so \
                   (set HERON_PLUGIN_SO, or use --no-build to read an existing sink)"
      return 1
    | some _ => runBuild fixDir.toString targets
  let reports ← readSink fixDir cli.paths
  let pal : Palette := { on := ← decideColor cli.color (cli.json || cli.apply) }
  emit reports pal cli.json cli.apply cli.fix
