import Heron.Check

open Lean Elab Command Parser Heron

private structure RedundantLetWildcardMatch where
  doLetStx : Syntax
  letKeyword : Syntax
  rhs : Syntax

/-- Check if a doLetArrow binds a wildcard `_` pattern. -/
private def isWildcardLetArrow? : Syntax → Option (Syntax × Syntax)
  | elem@`(doElem| let _ ← $rhs) => some (elem[0]!, rhs)
  | _ => none

/-- Find `let _ ← action` in do-blocks. -/
private def findRedundantLetWildcards (stx : Syntax) : Array RedundantLetWildcardMatch :=
  let doSeqs := Syntax.collectAll (fun s =>
    if s.getKind == ``Term.doSeqIndent || s.getKind == ``Term.doSeqBracketed then #[s]
    else #[]) stx
  doSeqs.flatMap fun doSeq =>
    let elems := getDoElems doSeq
    elems.filterMap fun elem =>
      match isWildcardLetArrow? elem with
      | some (letKw, rhs) =>
        some { doLetStx := elem, letKeyword := letKw, rhs }
      | none => none

@[check_rule] instance : Check RedundantLetWildcardMatch where
  name := `redundantLetWildcard
  severity := .information
  category := .simplification
  find := findRedundantLetWildcards
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
