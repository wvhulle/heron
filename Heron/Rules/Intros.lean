import Heron.Rules.Basic

open Lean Elab Command Heron.Rules

private def isIntroTactic (stx : Syntax) : Bool :=
  stx.getKind == ``Lean.Parser.Tactic.intro

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
    else if isIntroTactic stx then
      #[stx]
    else
      stx.getArgs.foldl (fun acc c => acc ++ flattenTacticSeq c) #[]
  go (tactics : Array Syntax) (i : Nat) (run : Array Syntax) (acc : Array (Array Syntax))
      : Array (Array Syntax) :=
    if h : i < tactics.size then
      let tac := tactics[i]
      if isIntroTactic tac then go tactics (i + 1) (run.push tac) acc
      else
        let acc' := if run.size > 1 then acc.push run else acc
        go tactics (i + 1) #[] acc'
    else if run.size > 1 then acc.push run
    else acc

private partial def getIntroIdents (stx : Syntax) : Array Syntax :=
  if stx.isIdent then #[stx]
  else if stx.getKind == ``Lean.Parser.Term.hole then #[stx]
  else stx.getArgs.foldl (fun acc c => acc ++ getIntroIdents c) #[]

private def detectIntros (stx : Syntax) : Array IntrosFixData :=
  (collectIntroRuns stx).filterMap fun run => do
    guard (1 < run.size)
    let allIdents := run.foldl (fun acc s => acc ++ getIntroIdents s) #[]
    let names := allIdents.map (·.getId.toString)
    let combined := "intro " ++ " ".intercalate names.toList
    let span ← mkSpan run[0]! run[run.size - 1]!
    return { diagStx := run[1]!, span, combined }

instance : Rule IntrosFixData where
  name := `testIntros
  detect := fun stx => return (detectIntros stx)
  diagStx := (·.diagStx)
  hintMsg := m!"Combine intros."
  diagMsg := m!"Sequential intros."
  toSuggestion := fun d => { suggestion := d.combined, span? := some d.span }

initialize Rule.initOption (α := IntrosFixData)
initialize Rule.addLinter (α := IntrosFixData)

namespace Tests

#eval Rule.addLinter (α := IntrosFixData)

#assertNoSuggests testIntros in
example (a b : Nat) : a = a := rfl

#assertNoSuggests testIntros in
example : Nat → Nat → True := by intro a; exact trivial

#assertEdits testIntros `(tactic| intro a; intro b) => `(tactic| intro a b) in
example : Nat → Nat → True := by intro a; intro b; exact trivial

end Tests
