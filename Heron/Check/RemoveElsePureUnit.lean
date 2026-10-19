module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure RemoveElsePureUnitMatch where
  ifStx : Syntax
  elseBranch : Syntax
  cond : Term
  thenBody : TSyntax ``Term.doSeq

/-- Check if a syntax node is `pure ()` or `pure Unit.unit`. -/
private meta def isPureUnit : Syntax → Bool
  | `(pure ()) => true
  | `(pure Unit.unit) => true
  | _ => false

private meta instance : Check RemoveElsePureUnitMatch where
  name := `removeElsePureUnit
  description := "Suggests dropping a redundant `else pure ()`."
  kinds := #[``Term.doIf]
  severity := .information
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | ifStx@`(doElem| if $cond then $thenBody else%$elseKeyword $body:term) =>
      if isPureUnit body then
        #[{ ifStx, elseBranch := mkNullNode #[elseKeyword, body], cond, thenBody }]
      else #[]
    | _ => #[]
  message := fun _ => m!"Redundant `else pure ()`"
  emphasize := fun m => m.elseBranch
  tags := #[.unnecessary]
  sources := #[.functionalProgrammingInLean "Single-branched if" "Monad-Transformers/More-do-Features/#single-branched-if"]
  explanation := fun _ => m!"In a do-block, `if cond then action else pure ()` can be simplified to `if cond then action`."
  replacements := some fun m => do
    let repl ← `(doElem| if $(m.cond) then $(m.thenBody))
    return #[{
      emphasizedSyntax := m.ifStx
      oldSyntax := m.ifStx
      newSyntax := repl
      prettyPrint := PrettyPrinter.ppCategory `doElem
      inlineViolationLabel := m!"else pure ()"
    }]

register_check RemoveElsePureUnitMatch
