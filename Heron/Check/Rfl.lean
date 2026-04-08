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
  pureDetect := fun stx => (findRflTactics stx).map ({ rflStx := · })
  message := fun _ => m!"Use `exact rfl`"
  node := fun m => m.rflStx
  reference := some { topic := "`rfl`", url := "https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality" }
  tags := #[.unnecessary]
  explanation := fun _ => m!"The bare `rfl` tactic is sugar for `exact rfl`. Using `exact rfl` is more explicit and consistent with other `exact` usages."
  replacements := fun m => do
    let rflId := mkIdent `rfl
    let repl ← `(tactic| exact $rflId)
    return #[{
      sourceNode := m.rflStx
      targetNode := m.rflStx
      insertText := repl
      category := `tactic
      sourceLabel := m!"bare rfl"
    }]

namespace Tests

#assertIgnore testRfl in example (a : Nat) : a = a + 0 := by simp

#assertCheck testRfl in
example (a : Nat) : a = a := by rfl
becomes `(example (a : Nat) : a = a := by exact rfl)

end Tests
