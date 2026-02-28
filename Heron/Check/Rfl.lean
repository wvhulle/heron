import Heron.Check
import Heron.Assert

open Lean Elab Command Heron

private structure RflMatch where
  rflStx : Syntax

private def findRflTactics : Syntax → Array Syntax :=
  Syntax.collectAll fun
    | stx@`(tactic| rfl) => #[stx]
    | _ => #[]

@[check_rule] instance : Check RflMatch where
  ruleName := `testRfl
  severity := .information
  category := .style
  detect := fun stx => return (findRflTactics stx).map ({ rflStx := · })
  message := fun _ => m!"Use `exact rfl`"
  node := fun m => m.rflStx
  reference := some { topic := "`rfl`", url := "https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality" }
  tags := #[.unnecessary]
  explanation := fun _ => m!"The bare `rfl` tactic is sugar for `exact rfl`. Using `exact rfl` is more explicit and consistent with other `exact` usages."
  replacements := fun m => #[{
    sourceNode := m.rflStx
    targetNode := m.rflStx
    insertText := "exact rfl"
    sourceLabel := m!"bare rfl"
  }]

namespace Tests

#assertIgnore testRfl in example (a : Nat) : a = a + 0 := by simp

#assertCheck testRfl in
example (a : Nat) : a = a := by rfl
becomes `(command| example (a : Nat) : a = a := by exact rfl)

end Tests
