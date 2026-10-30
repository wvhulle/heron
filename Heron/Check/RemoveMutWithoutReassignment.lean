module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure RemoveMutWithoutReassignmentMatch where
  doLetStx : Syntax
  ident : TSyntax `ident
  valStx : TSyntax `term
  immutableLetElement : TSyntax `doElem := ⟨.missing⟩

private meta def immutableLet (m : RemoveMutWithoutReassignmentMatch) : CommandElabM (TSyntax `doElem) :=
  `(doElem| let $m.ident := $m.valStx)

private meta def detectUnnecessaryMut (stx : Syntax) :
    CommandElabM (Array RemoveMutWithoutReassignmentMatch) := do
  let `(doElem| let mut $ident:ident := $valStx) := stx | return #[]
  let m := { doLetStx := stx, ident, valStx }
  return #[{ m with immutableLetElement := ← immutableLet m }]

private meta instance : Check RemoveMutWithoutReassignmentMatch where
  name := `removeMutWithoutReassignment
  description := "Suggests removing `mut` from a variable that is never reassigned."
  kinds := #[``Term.doLet]
  severity := .warning
  category := .simplification
  detect := detectUnnecessaryMut
  requiredRewrite := fun m => some (m.doLetStx, m.immutableLetElement)
  message := fun _ => m!"Remove unnecessary `mut`"
  emphasize := fun m => m.doLetStx
  sources := #[.functionalProgrammingInLean "`let mut`" "Monad-Transformers/More-do-Features/#let-mut"]
  tags := #[.unnecessary]
  explanation := fun _ => m!"This variable is declared `mut` but never reassigned. Use `let` instead of `let mut` to signal immutability."
  replacements := some fun m => do
    return #[{
      emphasizedSyntax := m.doLetStx
      oldSyntax := m.doLetStx
      newSyntax := m.immutableLetElement
      prettyPrint := PrettyPrinter.ppCategory `doElem
      inlineViolationLabel := m!"unused mut"
    }]

register_check RemoveMutWithoutReassignmentMatch
