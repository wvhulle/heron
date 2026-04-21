module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure RedundantElsePureUnitMatch where
  ifStx : Syntax
  elseBranch : Syntax
  cond : Syntax
  thenBody : Syntax

/-- Check if a syntax node is `pure ()` or `pure Unit.unit`. -/
private meta def isPureUnit : Syntax → Bool
  | `(pure ()) => true
  | `(pure Unit.unit) => true
  | _ => false

/-- Find `if cond then ... else pure ()` in do-blocks. -/
private meta def detectRedundantElsePureUnit : Syntax → Array RedundantElsePureUnitMatch
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

private meta def findRedundantElsePureUnit (stx : Syntax) : Array RedundantElsePureUnitMatch :=
  Syntax.collectAll detectRedundantElsePureUnit stx

private meta instance : Check RedundantElsePureUnitMatch where
  name := `redundantElsePureUnit
  severity := .information
  category := .simplification
  find := findRedundantElsePureUnit
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

meta initialize Check.register (α := RedundantElsePureUnitMatch)
