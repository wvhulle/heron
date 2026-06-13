module

public meta import Heron.Check
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure RedundantLetWildcardMatch where
  doLetStx : Syntax
  rhs : Syntax

/-- Match `let _ ← rhs`. -/
private meta def matchWildcardLetArrow? : Syntax → Option RedundantLetWildcardMatch
  | stx@`(doElem| let _ ← $rhs) => some { doLetStx := stx, rhs }
  | _ => none

private meta instance : Check RedundantLetWildcardMatch where
  name := `redundantLetWildcard
  kinds := #[``Term.doSeqIndent, ``Term.doSeqBracketed]
  severity := .information
  category := .simplification
  detect := fun stx => pure <| (getDoElems stx).filterMap matchWildcardLetArrow?
  message := fun _ => m!"Redundant `let _ ←`"
  emphasize := fun m => m.doLetStx
  tags := #[.unnecessary]
  reference := none
  explanation := fun _ => m!"`let _ ← action` can be simplified to just `action` in a do-block."
  replacements := fun m => return #[{
    emphasizedSyntax := m.doLetStx
    oldSyntax := m.doLetStx
    -- Drop the rhs's trailing trivia: a trailing comment lives there but sits *outside*
    -- `doLetStx`'s replaced range, so keeping it would duplicate the comment in the output.
    newSyntax := m.rhs.unsetTrailing
    inlineViolationLabel := m!"let _ ←"
  }]

meta initialize Check.register (α := RedundantLetWildcardMatch)
