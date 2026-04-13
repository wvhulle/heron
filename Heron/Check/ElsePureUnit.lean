import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure ElsePureUnitMatch where
  ifStx : Syntax
  elseBranch : Syntax
  cond : Syntax
  thenBody : Syntax

/-- Check if a syntax node is `pure ()` or `pure Unit.unit`. -/
private def isPureUnit : Syntax → Bool
  | `(pure ()) => true
  | `(pure Unit.unit) => true
  | _ => false

/-- Find `if cond then ... else pure ()` in do-blocks. -/
private def detectElsePureUnit : Syntax → Array ElsePureUnitMatch
  | s@`(doElem| if $cond then $thenBody else $elseBody) =>
    let elseElems := getDoElems elseBody
    if elseElems.size != 1 then #[]
    else
    let elem := elseElems[0]!
    let body := if elem.getKind == ``Term.doExpr then elem[0]! else elem
    if !isPureUnit body then #[]
    else
      #[{ ifStx := s, elseBranch := s.getArgs.back!, cond, thenBody }]
  | _ => #[]

private def findElsePureUnit (stx : Syntax) : Array ElsePureUnitMatch :=
  Syntax.collectAll detectElsePureUnit stx

@[check_rule] instance : Check ElsePureUnitMatch where
  name := `elsePureUnit
  severity := .information
  category := .simplification
  find := findElsePureUnit
  message := fun _ => m!"Redundant `else pure ()`"
  emphasize := fun m => m.elseBranch
  tags := #[.unnecessary]
  reference := some { topic := "Single-branched if", url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/do.html" }
  explanation := fun _ => m!"In a do-block, `if cond then action else pure ()` can be simplified to `if cond then action`."
  replacements := fun m => do
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

namespace Tests

#assertCheck elsePureUnit in
example : IO Unit := do
  if true then
    IO.println "hello"
  else
    pure ()
becomes `(command|
example : IO Unit := do
  if true then
    IO.println "hello")

#assertIgnore elsePureUnit in
  example : IO Unit := do
    if true then
      IO.println "hello"
    else
      IO.println "world"

#assertIgnore elsePureUnit in
  example : IO Unit := do
    if true then
      IO.println "hello"

end Tests
