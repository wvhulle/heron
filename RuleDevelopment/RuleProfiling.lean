module

public meta import Lean.Elab.Command
public meta import Heron.Check
meta import Lean.Linter.Basic

public section

open Lean Elab Command

namespace Heron

/-- A column definition for table rendering. -/
meta structure Column where
  header : String
  separator : Char := '─'

/-- Render a table with auto-expanding columns.
    Column widths expand to fit the widest cell in each column.
    Separator rows fill the full column width with the separator character. -/
meta def renderTable (columns : Array Column) (rows : Array (Array String)) : String :=
  let gap := 2
  let headers := columns.map (·.header)
  let widths := (#[headers] ++ rows).foldl (init := columns.map fun _ => 0) fun acc row =>
    Array.zipWith max acc (row.map (·.length))
  let pad (s : String) (w : Nat) := s.pushn ' ' (w - s.length + gap)
  let renderRow (cells : Array String) :=
    (Array.zipWith pad cells widths).toList |> String.join
  let sepLine := (Array.zipWith (fun c w => "".pushn c.separator w |>.pushn ' ' gap) columns widths).toList |> String.join
  String.intercalate "\n" ([renderRow headers, sepLine] ++ (rows.map renderRow).toList)

/-- Accumulated per-rule profiling data. -/
meta structure RuleProfile where
  elapsedNs : Nat := 0
  matchCount : Nat := 0
  callCount : Nat := 0

/-- Format nanoseconds as a millisecond string with 3 decimal places. -/
meta def fmtNanosAsMs (ns : Nat) : String :=
  let us := (ns + 500) / 1000
  let ms := us / 1000
  let frac := us % 1000
  let fracStr := toString frac
  let padded := "".pushn '0' (3 - fracStr.length) ++ fracStr
  s!"{ms}.{padded}ms"

/-- Convert a `RuleProfile` to a table row. -/
meta def RuleProfile.toRow (name : String) (p : RuleProfile) : Array String :=
  #[name, fmtNanosAsMs p.elapsedNs, toString p.matchCount, toString p.callCount]

private meta def profileColumns : Array Column :=
  #[⟨"Rule", '─'⟩, ⟨"Time", '─'⟩, ⟨"Matches", '─'⟩, ⟨"Calls", '─'⟩]

/-- Option to enable per-rule profiling accumulation (without trace output). -/
private meta def profilingOption : Lean.Option Bool :=
  { name := `heron.profile, defValue := false }

meta initialize
  Lean.registerOption `heron.profile
    { defValue := .ofBool false
      descr := "Accumulate per-rule profiling data for #heronProfile."
      name := `heron }

/-- Global accumulator for per-rule timing, gated behind `heron.profile`. -/
meta initialize profilingAccumulator : IO.Ref (Std.HashMap Name RuleProfile) ←
  IO.mkRef {}

/-- Record profiling data for a single rule invocation. -/
private meta def recordProfile (name : Name) (elapsedNs matchCount : Nat) : BaseIO Unit :=
  profilingAccumulator.modify fun map =>
    let prev := map.getD name {}
    map.insert name { prev with
      elapsedNs := prev.elapsedNs + elapsedNs
      matchCount := prev.matchCount + matchCount
      callCount := prev.callCount + 1 }

private meta def ruleProfilingLinter : Linter where
  name := `heronProfile
  run := withSetOptionIn fun stx => do
    let opts ← getOptions
    unless profilingOption.get opts do return
    if Heron.isReelaboratingGuardSet opts then return
    for entry in ← heronRuleRegistry.get do
      if entry.isEnabled opts then
        let start ← IO.monoNanosNow
        let findings ← entry.findActions stx
        recordProfile entry.name ((← IO.monoNanosNow) - start) findings.size

meta initialize lintersRef.modify (·.push ruleProfilingLinter)

syntax (name := heronProfileCmd) "#heronProfile" : command

@[command_elab heronProfileCmd]
meta def elabHeronProfile : CommandElab
  | stx => do
    let map ← profilingAccumulator.get
    if map.isEmpty then
      logInfoAt stx "No profiling data collected. Enable with: set_option heron.profile true"
      return
    let entries := map.fold (init := #[]) fun acc name profile => acc.push (name, profile)
    let sorted := entries.qsort fun a b => a.2.elapsedNs > b.2.elapsedNs
    let rows := sorted.map fun (name, p) => p.toRow (toString name)
    logInfoAt stx ("Heron profile:" ++ Format.line ++ renderTable profileColumns rows)
    profilingAccumulator.set {}

end Heron
