import Heron.Refactor
import Heron.Assert

open Lean Elab Command Heron

private structure FlipIfFixData where
  negCondStx : Syntax
  innerCond : Syntax
  thenBranch : Syntax
  elseBranch : Syntax

private def findFlipIfCandidates : Syntax → Array FlipIfFixData :=
  Syntax.collectAll fun
    | `(if $cond then $thenBr else $elseBr) =>
      match cond with
      | `(!$inner) => #[{ negCondStx := cond, innerCond := inner,
                           thenBranch := thenBr, elseBranch := elseBr }]
      | _ => #[]
    | _ => #[]

private def reprintTrimmed (stx : Syntax) : String :=
  (stx.reprint.getD "").trimAscii.toString

@[refactor_rule] instance : Refactor FlipIfFixData where
  ruleName := `flipIf
  detect := fun stx => return findFlipIfCandidates stx
  shortInstruction := fun _ => m!"Flip `if` branches"
  replacements := fun fd => #[
    { sourceNode := fd.negCondStx
      targetNode := fd.negCondStx
      insertText := reprintTrimmed fd.innerCond
      sourceLabel := m!"remove negation" },
    { sourceNode := fd.thenBranch
      targetNode := fd.thenBranch
      insertText := reprintTrimmed fd.elseBranch
      sourceLabel := m!"swap branches" },
    { sourceNode := fd.elseBranch
      targetNode := fd.elseBranch
      insertText := reprintTrimmed fd.thenBranch
      sourceLabel := m!"swap branches" }
  ]
  codeActionKind := "refactor.rewrite"

namespace Tests

#assertRefactor flipIf `(term| !p) => `(term| p), `(term| a) => `(term| b), `(term| b) => `(term| a) in
def flipMe (p : Bool) (a b : Nat) : Nat := if !p then a else b

#assertIgnore flipIf in
def noFlip (p : Bool) (a b : Nat) : Nat := if p then a else b

end Tests
