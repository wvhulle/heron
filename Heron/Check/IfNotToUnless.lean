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

private meta instance : Check IfNotToUnlessMatch where
  name := `ifNotToUnless
  kinds := #[``Term.doIf]
  severity := .information
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | s@`(doElem| if $cond then $thenBody) =>
      match isNegation? cond with
      | some inner => #[{ ifStx := s, innerCond := inner, thenBody }]
      | none => #[]
    | _ => #[]
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

meta initialize Check.register (α := IfNotToUnlessMatch)
