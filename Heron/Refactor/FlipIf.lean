import Heron.Refactor
import Heron.Assert

open Lean Elab Command Heron

private structure FlipIfMatch where
  negCondStx : Syntax
  innerCond : Syntax
  thenBranch : Syntax
  elseBranch : Syntax

private def findFlipIfCandidates : Syntax → Array FlipIfMatch :=
  Syntax.collectAll fun
    | `(if $cond then $thenBr else $elseBr) =>
      match cond with
      | `(!$inner) => #[{ negCondStx := cond, innerCond := inner,
                           thenBranch := thenBr, elseBranch := elseBr }]
      | _ => #[]
    | _ => #[]

private def reprintTrimmed (stx : Syntax) : String :=
  (stx.reprint.getD "").trimAscii.toString

@[refactor_rule] instance : Refactor FlipIfMatch where
  ruleName := `flipIf
  detect := fun stx => return findFlipIfCandidates stx
  message := fun _ => m!"Flip `if` branches"
  replacements := fun m => #[
    { sourceNode := m.negCondStx
      targetNode := m.negCondStx
      insertText := reprintTrimmed m.innerCond
      sourceLabel := m!"remove negation" },
    { sourceNode := m.thenBranch
      targetNode := m.thenBranch
      insertText := reprintTrimmed m.elseBranch
      sourceLabel := m!"swap branches" },
    { sourceNode := m.elseBranch
      targetNode := m.elseBranch
      insertText := reprintTrimmed m.thenBranch
      sourceLabel := m!"swap branches" }
  ]
  codeActionKind := "refactor.rewrite"

namespace Tests

#assertRefactor flipIf `(term| !p) => `(term| p), `(term| a) => `(term| b), `(term| b) => `(term| a) in
def flipMe (p : Bool) (a b : Nat) : Nat := if !p then a else b

#assertIgnore flipIf in
def noFlip (p : Bool) (a b : Nat) : Nat := if p then a else b

end Tests
