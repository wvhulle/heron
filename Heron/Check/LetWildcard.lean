import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure LetWildcardMatch where
  doLetStx : Syntax
  letKeyword : Syntax
  rhs : Syntax

/-- Check if a doLetArrow binds a wildcard `_` pattern. -/
private def isWildcardLetArrow? : Syntax → Option (Syntax × Syntax)
  | elem@`(doElem| let _ ← $rhs) => some (elem[0]!, rhs)
  | _ => none

/-- Find `let _ ← action` in do-blocks. -/
private def findLetWildcards (stx : Syntax) : Array LetWildcardMatch :=
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

@[check_rule] instance : Check LetWildcardMatch where
  ruleName := `letWildcard
  severity := .information
  category := .simplification
  pureDetect := findLetWildcards
  message := fun _ => m!"Redundant `let _ ←`"
  node := fun m => m.letKeyword
  tags := #[.unnecessary]
  reference := some { topic := "do-notation", url := "https://lean-lang.org/functional_programming_in_lean/hello-world/conveniences.html" }
  explanation := fun _ => m!"`let _ ← action` can be simplified to just `action` in a do-block."
  replacements := fun m => return #[{
    emphasizedSyntax := m.doLetStx
    oldSyntax := m.doLetStx
    newSyntax := m.rhs
    inlineViolationLabel := m!"let _ ←"
  }]

namespace Tests

#assertCheck letWildcard in
example : IO Unit := do
  let _ ← IO.println "hello"
  pure ()
becomes `(command|
example : IO Unit := do
  IO.println "hello"
  pure ())

#assertIgnore letWildcard in
example : IO Unit := do
  let x ← IO.getLine
  IO.println x

#assertIgnore letWildcard in
example : IO Unit := do
  IO.println "hello"

end Tests
