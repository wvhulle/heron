module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure ExprAppChainToMkAppNMatch where
  fullStx : Syntax
  fn : Syntax
  args : Array Syntax

/-- Collect a chain of nested `Expr.app`/`.app` calls, returning (innermost fn, args left-to-right).
Handles parenthesized inner expressions directly via quasiquote patterns. -/
private meta partial def collectAppChain : Syntax → Option (Syntax × Array Syntax)
  | `(Expr.app ($inner) $arg) =>
    match collectAppChain inner with
    | some (fn, args) => some (fn, args.push arg)
    | none => some (inner, #[arg])
  | `(Expr.app $inner $arg) =>
    match collectAppChain inner with
    | some (fn, args) => some (fn, args.push arg)
    | none => some (inner, #[arg])
  | `(.app ($inner) $arg) =>
    match collectAppChain inner with
    | some (fn, args) => some (fn, args.push arg)
    | none => some (inner, #[arg])
  | `(.app $inner $arg) =>
    match collectAppChain inner with
    | some (fn, args) => some (fn, args.push arg)
    | none => some (inner, #[arg])
  | _ => none

/-- Find chains of 2+ nested `Expr.app` / `.app` calls.
Walk top-down, skip children of matched chains to avoid duplicates. -/
private meta partial def findExprAppChains (stx : Syntax) : Array ExprAppChainToMkAppNMatch :=
  match collectAppChain stx with
  | some (fn, args) =>
    if args.size >= 2 then
      let fnResults := findExprAppChains fn
      let argResults := args.flatMap findExprAppChains
      #[{ fullStx := stx, fn, args }] ++ fnResults ++ argResults
    else
      stx.getArgs.flatMap findExprAppChains
  | none => stx.getArgs.flatMap findExprAppChains

private meta instance : Check ExprAppChainToMkAppNMatch where
  name := `exprAppChainToMkAppN
  severity := .information
  category := .simplification
  find := findExprAppChains
  message := fun _ => m!"Use `mkAppN` instead of nested `Expr.app`"
  emphasize := fun m => m.fullStx
  reference := some { topic := "Expressions", url := "https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html" }
  explanation := fun _ => m!"Chains of `Expr.app (Expr.app f a) b` can be simplified to `mkAppN f #[a, b]`."
  replacements := fun m => do
    let fn : TSyntax `term := ⟨m.fn⟩
    let args : TSyntaxArray `term := m.args.map (⟨·⟩)
    let mkAppNId := mkIdent `mkAppN
    let repl ← `($mkAppNId $fn #[$args,*])
    return #[{
      emphasizedSyntax := m.fullStx
      oldSyntax := m.fullStx
      newSyntax := repl
      inlineViolationLabel := m!"Expr.app chain → mkAppN"
    }]

meta initialize Check.register (α := ExprAppChainToMkAppNMatch)
