import FixReporting.FixReportRendering
import FixReporting.LintSubcommand.BuildFixSink

/-!
# `heron lint` — build-integrated Heron fix reporter (clippy model)

Drives `lake build` with Heron loaded as a `lean --plugin` so the linter runs on every module and
writes its fixes to a sink during the build, then reads + renders them. Lake's incremental build is
the cache — no re-elaboration, no cache of our own. Requires the consumer's `lakefile.lean` to load
the plugin (`plugins := #[`@heron/plugin]`); registering it as `lintDriver := "heron/heron"` with
`lintDriverArgs := #["lint"]` makes it the project's `lake lint`.

    lake lint                       # build all libraries + report all fixes
    lake lint -- Sparkle.Analog     # restrict build + report to lake targets
    lake lint -- --json | jq
    lake lint -- --fix              # rewrite files in place
    lake lint -- --no-build         # read the existing sink only
-/

open Cli FixReporting

def runLint (parsed : Parsed) : IO UInt32 := do
  let requestedTargets := parsed.variableArgsAs! String
  let fixDir : System.FilePath := ".lake" / "build" / "heron-fixes"
  let targets ← if requestedTargets.isEmpty then localLibNames else pure requestedTargets
  unless parsed.hasFlag "no-build" do
    match ← ensurePluginSo with
    | none =>
      IO.eprintln "heron lint: could not build or locate the Heron plugin \
                   (set HERON_PLUGIN_SO, or use --no-build to read an existing sink)"
      return 1
    | some _ => runBuild fixDir.toString targets
  let reports ← readSink fixDir requestedTargets.toList
  let json := parsed.hasFlag "json"
  let apply := parsed.hasFlag "apply"
  let pal : Palette := { on := ← decideColor (requestedColor parsed) (json || apply) }
  emit reports pal json apply (parsed.hasFlag "fix")

def lintCmd : Cmd := `[Cli|
  lint VIA runLint;
  "Build Lake targets with the Heron plugin and report the fixes it recorded. \
   `lake lint` runs this when the lakefile sets `lintDriverArgs := #[\"lint\"]`."

  FLAGS:
    fix;        "Rewrite the files in place."
    apply;      "Print the one matching file with every fix applied."
    json;       "Print the fixes as JSON."
    color;      "Color the output even when stdout is not a terminal."
    "no-color"; "Never color the output."
    "no-build"; "Read the fixes recorded by the last build instead of building."

  ARGS:
    ...targets : String; "Lake targets to build and report on; every library of the workspace by default."
]
