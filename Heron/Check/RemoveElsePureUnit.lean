module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure RemoveElsePureUnitMatch where
  ifStx : Syntax
  elseBranch : Syntax
  cond : Syntax
  thenBody : Syntax

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
    | s@`(doElem| if $cond then $thenBody else $body:term) =>
      if isPureUnit body then #[{ ifStx := s, elseBranch := s.getArgs.back!, cond, thenBody }]
      else #[]
    | _ => #[]
  message := fun _ => m!"Redundant `else pure ()`"
  emphasize := fun m => m.elseBranch
  tags := #[.unnecessary]
  sources := #[.functionalProgrammingInLean "Single-branched if" "Monad-Transformers/More-do-Features/#single-branched-if"]
  explanation := fun _ => m!"In a do-block, `if cond then action else pure ()` can be simplified to `if cond then action`."
  replacements := some fun m => do
    let cond : TSyntax `term := ⟨m.cond⟩
    let thenBody : TSyntax ``Term.doSeq := ⟨m.thenBody⟩
    let repl ← `(doElem| if $cond then $thenBody)
    return #[{
      emphasizedSyntax := m.ifStx
      oldSyntax := m.ifStx
      newSyntax := repl
      category := `doElem
      inlineViolationLabel := m!"else pure ()"
    }]

register_check RemoveElsePureUnitMatch
