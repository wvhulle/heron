import Lean.Elab.Command
import Lean.Meta.Hint

/-! ## Test linters for exercising `#assertSuggests` / `#assertNoSuggests`

These are minimal linters used purely for testing the assertion commands. -/

open Lean Elab Command

/-! ### testRfl: detects `rfl` tactic and suggests `exact rfl` -/

register_option linter.testRfl : Bool := {
  defValue := false
  descr := "test linter: suggest `exact rfl` instead of `rfl`"
}

private def isBareTactic (stx : Syntax) (name : String) : Bool :=
  stx.getArgs.any fun a => if let .atom _ v := a then v == name else false

private def isTacticNode (stx : Syntax) : Bool :=
  stx.getKind.toString.startsWith "Lean.Parser.Tactic."

private partial def findRflTactics (stx : Syntax) : Array Syntax :=
  if isTacticNode stx && isBareTactic stx "rfl" then #[stx]
  else stx.getArgs.foldl (fun acc child => acc ++ findRflTactics child) #[]

private def testRflLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.testRfl.get (← getOptions) do return
  for rflStx in findRflTactics stx do
    let suggestion : Meta.Hint.Suggestion := {
      suggestion := "exact rfl"
      span? := some rflStx
    }
    let hint ← liftCoreM <| MessageData.hint m!"Use `exact rfl`." #[suggestion]
    Linter.logLint linter.testRfl rflStx (m!"Bare `rfl` detected." ++ hint)

initialize addLinter testRflLinter

/-! ### testIntros: detects sequential `intro` and suggests combining them -/

register_option linter.testIntros : Bool := {
  defValue := false
  descr := "test linter: combine sequential intros"
}

private partial def collectIntroRuns (stx : Syntax) : Array (Array Syntax) :=
  let tactics := flattenTacticSeq stx
  go tactics 0 #[] #[]
where
  flattenTacticSeq (stx : Syntax) : Array Syntax :=
    if stx.getKind == ``Lean.Parser.Tactic.tacticSeq ||
       stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      stx.getArgs.foldl (fun acc c => acc ++ flattenTacticSeq c) #[]
    else if isBareTactic stx "intro" then
      #[stx]
    else
      stx.getArgs.foldl (fun acc c => acc ++ flattenTacticSeq c) #[]
  go (tactics : Array Syntax) (i : Nat) (run : Array Syntax) (acc : Array (Array Syntax))
      : Array (Array Syntax) :=
    if h : i < tactics.size then
      let tac := tactics[i]
      if isBareTactic tac "intro" then go tactics (i + 1) (run.push tac) acc
      else
        let acc' := if run.size > 1 then acc.push run else acc
        go tactics (i + 1) #[] acc'
    else if run.size > 1 then acc.push run
    else acc

private def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private partial def getIntroIdents (stx : Syntax) : Array Syntax :=
  if stx.isIdent then #[stx]
  else if stx.getKind == ``Lean.Parser.Term.hole then #[stx]
  else if let .atom _ v := stx then
    if v == "intro" then #[] else #[]
  else stx.getArgs.foldl (fun acc c => acc ++ getIntroIdents c) #[]

private def testIntrosLinter : Linter where run := withSetOptionIn fun stx => do
  unless linter.testIntros.get (← getOptions) do return
  for run in collectIntroRuns stx do
    if h : 1 < run.size then
      let allIdents := run.foldl (fun acc s => acc ++ getIntroIdents s) #[]
      let names := allIdents.map (·.getId.toString)
      let combined := "intro " ++ " ".intercalate names.toList
      let suggestion : Meta.Hint.Suggestion := {
        suggestion := combined
        span? := mkSpan run[0]! run[run.size - 1]!
      }
      let hint ← liftCoreM <| MessageData.hint m!"Combine intros." #[suggestion]
      Linter.logLint linter.testIntros run[1] (m!"Sequential intros." ++ hint)

initialize addLinter testIntrosLinter
