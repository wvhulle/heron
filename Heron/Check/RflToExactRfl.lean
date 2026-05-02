module

public meta import Heron.Check

open Lean Elab Command Heron

private structure RflToExactRflMatch where
  rflStx : Syntax

private meta instance : Check RflToExactRflMatch where
  name := `rflToExactRfl
  kinds := #[``Lean.Parser.Tactic.tacticRfl]
  severity := .information
  category := .style
  detect := fun stx => pure <|
    match stx with
    | `(tactic| rfl) => #[{ rflStx := stx }]
    | _ => #[]
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

meta initialize Check.register (α := RflToExactRflMatch)
