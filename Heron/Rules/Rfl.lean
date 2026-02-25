import Heron.Provider.Diagnostic
import Heron.AssertFix
import Heron.AssertIgnore

open Lean Elab Command Heron.Provider

private structure RflFixData where
  rflStx : Syntax

private partial def findRflTactics (stx : Syntax) : Array Syntax :=
  if let `(tactic| rfl) := stx then #[stx] else stx.getArgs.foldl (fun acc child => acc ++ findRflTactics child) #[]

@[diagnostic_rule] instance : Diagnostic RflFixData where
  ruleName := `testRfl
  severity := .information
  detect := fun stx => return (findRflTactics stx).map ({ rflStx := · })
  hintMessage := fun _ => m!"Use `exact rfl`."
  diagnosticMessage := m!"Bare `rfl` detected."
  replacements := fun fd => #[{
    sourceNode := fd.rflStx
    targetNode := fd.rflStx
    insertText := "exact rfl"
    sourceLabel := m!"bare rfl"
  }]
  diagnosticTags := #[.unnecessary]

namespace Tests

#assertIgnore testRfl in example (a : Nat) : a = a + 0 := by simp

#assertFix testRfl `(tactic| rfl) => `(tactic| exact rfl) in example (a : Nat) : a = a := by rfl

end Tests
