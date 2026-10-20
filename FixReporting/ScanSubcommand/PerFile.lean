import Lean
import Heron
import FixReporting.FixReportRendering
import FixReporting.ScanSubcommand.Elaboration

/-! **Per-file engine.** Import each file's own full environment (`processHeader`) and detect.
Simplest and most faithful per file (and backs stdin), but re-imports the whole environment
(Mathlib etc.) for every file — use `SharedEnv` for whole trees. -/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Frontend Lean.Parser

namespace FixReporting

/-- Lint one source (labelled `label`, written back to `path` if given) with `checks`. Seeds
`linter.heron := true`; in-file `set_option`s still apply. Throws if imports fail. -/
def lintSourceCore (all : Bool) (checks : Array Heron.RuleEntry) (path : Option String)
    (label source : String) : IO Report := do
  let inputCtx := mkInputContext source label
  let (header, parserState, msgs) ← parseHeader inputCtx
  let opts := scanOptions
  let (env, msgs) ← processHeader header opts msgs inputCtx
  if msgs.hasErrors then
    for m in msgs.toList do IO.eprintln (← m.toString)
    throw <| IO.userError s!"failed to load imports of {label}"
  let fst : Frontend.State :=
    { commandState := Command.mkState env msgs opts, parserState, cmdPos := parserState.pos }
  let (_, (fixes, _)) ← IO.FS.withIsolatedStreams (((collectLoop all true checks #[]).run { inputCtx }).run fst)
  return { path, label, fileMap := inputCtx.fileMap, fixes }

def lintPerFile (all : Bool) (checks : Array Heron.RuleEntry) (file : String) : IO Report := do
  lintSourceCore all checks (some file) file (← IO.FS.readFile file)

def lintStdin (all : Bool) (checks : Array Heron.RuleEntry) (source : String) : IO Report :=
  lintSourceCore all checks none "<stdin>" source

end FixReporting
