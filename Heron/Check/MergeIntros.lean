module

public meta import Heron.Check

open Lean Elab Command Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private meta def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure MergeIntrosMatch where
  secondIntro : Syntax
  fullRange : Syntax
  allIntros : Array Syntax

private meta def introIdents : Syntax → Array Syntax :=
  Syntax.collectAll fun stx => if stx.isIdent || stx.getKind == ``Lean.Parser.Term.hole then #[stx] else #[]

/-- Collect tactic child nodes from the argument array of a `sepByIndent`
tactic sequence. In that layout, element/separator positions alternate starting
with an element at index 0. -/
private meta def tacticsOf (args : Array Syntax) : Array Syntax :=
  (args.mapIdx fun i s => (i, s)).filterMap fun (i, s) =>
    if i % 2 == 0 then some s else none

/-- Find maximal runs of two-or-more consecutive `intro` tactics within a single
tactic sequence. Runs that are interrupted by any other tactic are split. -/
private meta def introRunsIn (tactics : Array Syntax) : Array (Array Syntax) := Id.run do
  let mut runs : Array (Array Syntax) := #[]
  let mut current : Array Syntax := #[]
  for tac in tactics do
    if tac.getKind == ``Lean.Parser.Tactic.intro then
      current := current.push tac
    else
      if current.size ≥ 2 then runs := runs.push current
      current := #[]
  if current.size ≥ 2 then runs := runs.push current
  runs

/-- Walk syntax tree, collecting mergeable runs of consecutive `intro` tactics
from each tactic sequence encountered. -/
private meta partial def detectIntros (stx : Syntax) : Array MergeIntrosMatch := Id.run do
  let mut found : Array MergeIntrosMatch := #[]
  let k := stx.getKind
  let seqArgs : Option (Array Syntax) :=
    if k == ``Lean.Parser.Tactic.tacticSeq1Indented then some stx[0]!.getArgs
    else if k == ``Lean.Parser.Tactic.tacticSeqBracketed then some stx[1]!.getArgs
    else none
  if let some args := seqArgs then
    for run in introRunsIn (tacticsOf args) do
      if let some fullRange := mkSpan run[0]! run.back! then
        found := found.push { secondIntro := run[1]!, fullRange, allIntros := run }
  for child in stx.getArgs do
    found := found ++ detectIntros child
  return found

private meta instance : Check MergeIntrosMatch where
  name := `mergeIntros
  severity := .warning
  category := .simplification
  find := detectIntros
  message := fun _ => m!"Merge intros"
  emphasize := fun m => m.secondIntro
  tags := #[.unnecessary]
  explanation := fun _ =>
    m!"Multiple sequential `intro` tactics can be merged into one. This reduces tactic noise and is idiomatic Lean style."
  replacements := fun m => do
    let names : TSyntaxArray `ident := (m.allIntros.flatMap introIdents).map (⟨·⟩)
    let repl ← `(tactic| intro $names*)
    return #[{
          emphasizedSyntax := m.secondIntro
          oldSyntax := m.fullRange
          newSyntax := repl
          category := `tactic
          inlineViolationLabel := m!"sequential intro" }]

meta initialize Check.register (α := MergeIntrosMatch)
