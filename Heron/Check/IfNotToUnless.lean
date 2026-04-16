module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure IfNotToUnlessMatch where
  ifStx : Syntax
  innerCond : Syntax
  thenBody : Syntax

/-- Check if a condition is a negation: `not e`, `!e`, or `Not e`. -/
private meta def isNegation? : Syntax → Option Syntax
  | `(not $inner) => some inner
  | `(!$inner) => some inner
  | `(Not $inner) => some inner
  | _ => none

/-- Find `if not cond then body` (no else) in do-blocks. -/
private meta def detectIfNotToUnless : Syntax → Array IfNotToUnlessMatch
  | s@`(doElem| if $cond then $thenBody) =>
    match isNegation? cond with
    | some inner => #[{ ifStx := s, innerCond := inner, thenBody }]
    | none => #[]
  | _ => #[]

private meta def findIfNotToUnless (stx : Syntax) : Array IfNotToUnlessMatch :=
  Syntax.collectAll detectIfNotToUnless stx

@[check_rule] private meta instance : Check IfNotToUnlessMatch where
  name := `ifNotToUnless
  severity := .information
  category := .simplification
  find := findIfNotToUnless
  message := fun _ => m!"Use `unless` instead of `if not`"
  emphasize := fun m => m.ifStx
  reference := some { topic := "unless", url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/do.html" }
  explanation := fun _ => m!"In a do-block, `if not cond then body` can be simplified to `unless cond do body`."
  replacements := fun m => do
    let cond : TSyntax `term := ⟨m.innerCond⟩
    let thenBody : TSyntax ``Term.doSeq := ⟨m.thenBody⟩
    let repl ← `(doElem| unless $cond do $thenBody)
    return #[{
      emphasizedSyntax := m.ifStx
      oldSyntax := m.ifStx
      newSyntax := repl
      category := `doElem
      inlineViolationLabel := m!"if not → unless"
    }]
