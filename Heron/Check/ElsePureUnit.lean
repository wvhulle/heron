import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure ElsePureUnitMatch where
  ifStx : Syntax
  elseBranch : Syntax
  replacement : String

/-- Check if a syntax node is `pure ()` or `pure Unit.unit`. -/
private def isPureUnit : Syntax → Bool
  | `(pure ())          => true
  | `(pure Unit.unit)   => true
  | _                   => false

/-- Find `if cond then ... else pure ()` in do-blocks. -/
private def detectElsePureUnit : Syntax → Array ElsePureUnitMatch
  | s@`(doElem| if $_ then $_ else $elseBody) =>
    let elseElems := getDoElems elseBody
    if elseElems.size != 1 then #[]
    else
    let elem := elseElems[0]!
    let body := if elem.getKind == ``Term.doExpr then elem[0]! else elem
    if !isPureUnit body then #[]
    else
      let args := s.getArgs
      let withoutElse := args.pop
      let repl := String.join (withoutElse.map fun arg =>
        arg.reprint.getD "").toList
      #[{ ifStx := s, elseBranch := args.back!, replacement := repl.trimAsciiEnd.toString }]
  | _ => #[]

private def findElsePureUnit (stx : Syntax) : Array ElsePureUnitMatch :=
  Syntax.collectAll detectElsePureUnit stx

@[check_rule] instance : Check ElsePureUnitMatch where
  ruleName := `elsePureUnit
  severity := .information
  category := .simplification
  pureDetect := findElsePureUnit
  message := fun _ => m!"Redundant `else pure ()`"
  node := fun m => m.elseBranch
  tags := #[.unnecessary]
  reference := some { topic := "Single-branched if", url := "https://lean-lang.org/functional_programming_in_lean/monad-transformers/do.html" }
  explanation := fun _ => m!"In a do-block, `if cond then action else pure ()` can be simplified to `if cond then action`."
  replacements := fun m => #[{
    sourceNode := m.ifStx
    targetNode := m.ifStx
    insertText := m.replacement
    sourceLabel := m!"else pure ()"
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
