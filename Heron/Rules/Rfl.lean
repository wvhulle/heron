import Heron.AssertSuggests
import Heron.AssertEdits
import Heron.AssertNoSuggests
import Lean.Meta.Hint

open Lean Elab Command

/-- Option accessor created without `register_option` to avoid `initialize` timing issues. -/
private def linterTestRfl : Lean.Option Bool := { name := `linter.testRfl, defValue := false }

private structure RflFixData where
  rflStx : Syntax

private def isBareTactic (stx : Syntax) (name : String) : Bool :=
  stx.getArgs.any fun a => if let .atom _ v := a then v == name else false

private def isTacticNode (stx : Syntax) : Bool :=
  stx.getKind.toString.startsWith "Lean.Parser.Tactic."

private partial def findRflTactics (stx : Syntax) : Array Syntax :=
  if isTacticNode stx && isBareTactic stx "rfl" then #[stx]
  else stx.getArgs.foldl (fun acc child => acc ++ findRflTactics child) #[]

private def detect (stx : Syntax) : Array RflFixData :=
  (findRflTactics stx).map ({ rflStx := · })

private def toSuggestion (data : RflFixData) : Meta.Hint.Suggestion :=
  { suggestion := "exact rfl", span? := some data.rflStx }

private def rflLinter : Linter where run := withSetOptionIn fun stx => do
  unless linterTestRfl.get (← getOptions) do return
  for fixData in detect stx do
    let hint ← liftCoreM <| MessageData.hint m!"Use `exact rfl`." #[toSuggestion fixData]
    Linter.logLint linterTestRfl fixData.rflStx (m!"Bare `rfl` detected." ++ hint)

#eval addLinter rflLinter

/-! ## Tests -/

#assertNoSuggests testRfl in
example (a : Nat) : a = a + 0 := by simp

#assertNoSuggests in
example (a : Nat) : a = a := rfl

#assertNoSuggests in
example : True := trivial

#assertSuggests testRfl `(tactic| rfl) => `(tactic| exact rfl) in
example (a : Nat) : a = a := by rfl

#assertEdits testRfl `(tactic| rfl) => `(tactic| exact rfl) in
example (a : Nat) : a = a := by rfl
