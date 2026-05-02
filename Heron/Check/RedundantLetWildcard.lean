module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure RedundantLetWildcardMatch where
  doLetStx : Syntax
  letKeyword : Syntax
  rhs : Syntax

/-- Check if a doLetArrow binds a wildcard `_` pattern. -/
private meta def isWildcardLetArrow? : Syntax → Option (Syntax × Syntax)
  | elem@`(doElem| let _ ← $rhs) => some (elem[0]!, rhs)
  | _ => none

private meta def detectRedundantLetWildcards (doSeq : Syntax) : Array RedundantLetWildcardMatch :=
  let elems := getDoElems doSeq
  elems.filterMap fun elem =>
    match isWildcardLetArrow? elem with
    | some (letKw, rhs) =>
      some { doLetStx := elem, letKeyword := letKw, rhs }
    | none => none

private meta instance : Check RedundantLetWildcardMatch where
  name := `redundantLetWildcard
  kinds := #[``Term.doSeqIndent, ``Term.doSeqBracketed]
  severity := .information
  category := .simplification
  detect := fun stx => pure (detectRedundantLetWildcards stx)
  message := fun _ => m!"Redundant `let _ ←`"
  emphasize := fun m => m.letKeyword
  tags := #[.unnecessary]
  reference := none
  explanation := fun _ => m!"`let _ ← action` can be simplified to just `action` in a do-block."
  replacements := fun m => return #[{
    emphasizedSyntax := m.doLetStx
    oldSyntax := m.doLetStx
    newSyntax := m.rhs
    inlineViolationLabel := m!"let _ ←"
  }]

meta initialize Check.register (α := RedundantLetWildcardMatch)
