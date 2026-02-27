import Heron.Diagnostic
import Heron.Assert

open Lean Elab Command Heron

private structure RflFixData where
  rflStx : Syntax

private def findRflTactics : Syntax → Array Syntax :=
  Syntax.collectAll fun
    | stx@`(tactic| rfl) => #[stx]
    | _ => #[]

@[diagnostic_rule] instance : Diagnostic RflFixData where
  ruleName := `testRfl
  severity := .information
  detect := fun stx => return (findRflTactics stx).map ({ rflStx := · })
  hintMessage := fun _ => m!"Use `exact rfl`."
  diagnosticMessage := m!"Use `exact rfl` instead"
  violationNode := fun fd => fd.rflStx
  diagnosticTags := #[.unnecessary]
  replacements := fun fd => #[{
    sourceNode := fd.rflStx
    targetNode := fd.rflStx
    insertText := "exact rfl"
    sourceLabel := m!"bare rfl"
  }]

namespace Tests

#assertIgnore testRfl in example (a : Nat) : a = a + 0 := by simp

#assertFix testRfl `(tactic| rfl) => `(tactic| exact rfl) in example (a : Nat) : a = a := by rfl

end Tests
