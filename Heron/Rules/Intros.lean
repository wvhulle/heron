import Heron.AssertSuggests
import Heron.AssertEdits
import Heron.AssertNoSuggests
import Lean.Meta.Hint

open Lean Elab Command

private def linterTestIntros : Lean.Option Bool := { name := `linter.testIntros, defValue := false }

private def isBareTactic (stx : Syntax) (name : String) : Bool :=
  stx.getArgs.any fun a => if let .atom _ v := a then v == name else false

private def isTacticNode (stx : Syntax) : Bool :=
  stx.getKind.toString.startsWith "Lean.Parser.Tactic."

private structure IntrosFixData where
  diagStx : Syntax
  span : Syntax
  combined : String

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

private def detect (stx : Syntax) : Array IntrosFixData :=
  (collectIntroRuns stx).filterMap fun run => do
    guard (1 < run.size)
    let allIdents := run.foldl (fun acc s => acc ++ getIntroIdents s) #[]
    let names := allIdents.map (·.getId.toString)
    let combined := "intro " ++ " ".intercalate names.toList
    let span ← mkSpan run[0]! run[run.size - 1]!
    return { diagStx := run[1]!, span, combined }

private def toSuggestion (data : IntrosFixData) : Meta.Hint.Suggestion :=
  { suggestion := data.combined, span? := some data.span }

private def introsLinter : Linter where run := withSetOptionIn fun stx => do
  unless linterTestIntros.get (← getOptions) do return
  for fixData in detect stx do
    let hint ← liftCoreM <| MessageData.hint m!"Combine intros." #[toSuggestion fixData]
    Linter.logLint linterTestIntros fixData.diagStx (m!"Sequential intros." ++ hint)

#eval addLinter introsLinter

/-! ## Tests -/

#assertNoSuggests testIntros in
example (a b : Nat) : a = a := rfl

#assertNoSuggests testIntros in
example : Nat → Nat → True := by intro a; exact trivial

#assertEdits testIntros `(tactic| intro a; intro b) => `(tactic| intro a b) in
example : Nat → Nat → True := by intro a; intro b; exact trivial
