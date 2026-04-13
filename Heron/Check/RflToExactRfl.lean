import Heron.Check
import Heron.Assert

open Lean Elab Command Heron

private structure RflToExactRflMatch where
  rflStx : Syntax

private def findRflTactics : Syntax → Array Syntax :=
  Syntax.collectAll fun
    | stx@`(tactic| rfl) => #[stx]
    | _ => #[]

@[check_rule] instance : Check RflToExactRflMatch where
  name := `rflToExactRfl
  severity := .information
  category := .style
  find := fun stx => (findRflTactics stx).map fun s => { rflStx := s }
  message := fun _ => m!"Use `exact rfl`"
  emphasize := fun m => m.rflStx
  reference := some { topic := "`rfl`", url := "https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality" }
  tags := #[.unnecessary]
  explanation := fun _ => m!"The bare `rfl` tactic is sugar for `exact rfl`. Using `exact rfl` is more explicit and consistent with other `exact` usages."
  replacements := fun m => do
    let rflId := mkIdent `rfl
    let repl ← `(tactic| exact $rflId)
    return #[{
      emphasizedSyntax := m.rflStx
      oldSyntax := m.rflStx
      newSyntax := repl
      category := `tactic
      inlineViolationLabel := m!"bare rfl"
    }]

namespace Tests

#assertIgnore rflToExactRfl in example (a : Nat) : a = a + 0 := by simp

#assertCheck rflToExactRfl in
example (a : Nat) : a = a := by rfl
becomes `(example (a : Nat) : a = a := by exact rfl)

end Tests
