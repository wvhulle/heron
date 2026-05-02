module

public meta import Heron.Refactor

open Lean Elab Command Heron

private structure FlipIfMatch where
  negCondStx : Syntax
  innerCond : Syntax
  thenBranch : Syntax
  elseBranch : Syntax

private meta instance : Refactor FlipIfMatch where
  name := `flipIf
  kinds := #[``termIfThenElse]
  detect := fun stx => pure <|
    match stx with
    | `(if $cond then $thenBr else $elseBr) =>
      match cond with
      | `(!$inner) => #[{ negCondStx := cond, innerCond := inner,
                           thenBranch := thenBr, elseBranch := elseBr }]
      | _ => #[]
    | _ => #[]
  message := fun _ => m!"Flip `if` branches"
  replacements := fun m => return #[
    { emphasizedSyntax := m.negCondStx
      oldSyntax := m.negCondStx
      newSyntax := m.innerCond
      inlineViolationLabel := m!"remove negation" },
    { emphasizedSyntax := m.thenBranch
      oldSyntax := m.thenBranch
      newSyntax := m.elseBranch
      inlineViolationLabel := m!"swap branches" },
    { emphasizedSyntax := m.elseBranch
      oldSyntax := m.elseBranch
      newSyntax := m.thenBranch
      inlineViolationLabel := m!"swap branches" }
  ]
  codeActionKind := "refactor.rewrite"

@[code_action_provider]
public meta def flipIfProvider := Refactor.toCodeActionProvider (α := FlipIfMatch)

meta initialize Refactor.register (α := FlipIfMatch)
