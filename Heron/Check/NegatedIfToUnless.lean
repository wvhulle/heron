module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure NegatedIfToUnlessMatch where
  ifStx : Syntax
  innerCond : Term
  thenBody : TSyntax ``Term.doSeq

private meta def negatedCondition? : Term → Option Term
  | `(!$inner) | `(not $inner) | `(Not $inner) => some inner
  | _ => none

private meta instance : Check NegatedIfToUnlessMatch where
  name := `negatedIfToUnless
  description := "Suggests `unless` instead of `if not` without an `else` branch."
  kinds := #[``Term.doIf]
  severity := .information
  category := .simplification
  detect := fun stx => pure <| Option.toArray do
    let `(doElem| if $cond:term then $thenBody) := stx | none
    return { ifStx := stx, innerCond := ← negatedCondition? cond, thenBody }
  message := fun _ => m!"Use `unless` instead of `if not`"
  emphasize := fun m => m.ifStx
  sources := #[
    .functionalProgrammingInLean "unless" "Monad-Transformers/More-do-Features/#single-branched-if",
    .hlint "when (not x) ==> unless x"]
  explanation := fun _ => m!"In a do-block, `if not cond then body` can be simplified to `unless cond do body`."
  replacements := some fun m => return #[{
    emphasizedSyntax := m.ifStx
    oldSyntax := m.ifStx
    newSyntax := ← `(doElem| unless $m.innerCond do $m.thenBody)
    prettyPrint := PrettyPrinter.ppCategory `doElem
    inlineViolationLabel := m!"if not → unless" }]

register_check NegatedIfToUnlessMatch
