module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure RemoveElsePureUnitMatch where
  elseBranch : Syntax
  lastThenElem : TSyntax `doElem
  lastThenElemThroughElse : Syntax

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
  detect := fun stx => pure <| Option.toArray do
    let `(doElem| if $_ then $thenBody else%$elseKeyword $body:term) := stx | none
    guard (isPureUnit body)
    let lastThenElem ← (getDoElems thenBody).back?
    return { elseBranch := mkNullNode #[elseKeyword, body], lastThenElem,
             lastThenElemThroughElse := mkNullNode #[lastThenElem, elseKeyword, body] }
  message := fun _ => m!"Redundant `else pure ()`"
  emphasize := fun m => m.elseBranch
  tags := #[.unnecessary]
  sources := #[.functionalProgrammingInLean "Single-branched if" "Monad-Transformers/More-do-Features/#single-branched-if"]
  explanation := fun _ => m!"In a do-block, `if cond then action else pure ()` can be simplified to `if cond then action`."
  replacements := some fun m => return #[{
    emphasizedSyntax := m.elseBranch
    oldSyntax := m.lastThenElemThroughElse
    newSyntax := m.lastThenElem
    prettyPrint := PrettyPrinter.ppCategory `doElem
    inlineViolationLabel := m!"else pure ()" }]

register_check RemoveElsePureUnitMatch
