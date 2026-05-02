module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure ExprAppChainToMkAppNMatch where
  fullStx : Syntax
  fn : Syntax
  args : Array Syntax

/-- A single `Expr.app f a` or `.app f a` node, decomposed. -/
private structure AppNode where
  fn : Syntax
  arg : Syntax

/-- A flattened left-deep app chain: `f a₁ … aₙ`. -/
private structure AppChain where
  innermostFn : Syntax
  args : Array Syntax

/-- Strip one layer of parentheses, if present. -/
private meta def stripParen : Syntax → Syntax
  | `(($inner)) => inner
  | s => s

/-- Match `Expr.app f a` or `.app f a`. -/
private meta def matchApp? : Syntax → Option AppNode
  | `(Expr.app $fn $arg) => some { fn, arg }
  | `(.app $fn $arg) => some { fn, arg }
  | _ => none

/-- Collect a chain of nested `Expr.app`/`.app` calls. -/
private meta partial def collectAppChain (stx : Syntax) : Option AppChain := do
  let { fn, arg } ← matchApp? (stripParen stx)
  match collectAppChain fn with
  | some chain =>
    some { chain with args := chain.args.push arg }
  | none =>
    some { innermostFn := fn, args := #[arg] }

private meta instance : Check ExprAppChainToMkAppNMatch
    where
  name := `exprAppChainToMkAppN
  kinds := #[``Term.app]
  severity := .information
  category := .simplification
  detect := fun stx => pure <|
    match collectAppChain stx with
    | some { innermostFn, args } =>
      if args.size >= 2 then #[{ fullStx := stx, fn := innermostFn, args }] else #[]
    | none => #[]
  consumesSubtree := true
  message := fun _ => m!"Use `mkAppN` instead of nested `Expr.app`"
  emphasize := fun m => m.fullStx
  reference :=
    some
      { topic := "Expressions",
        url := "https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html" }
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
          inlineViolationLabel := m!"Expr.app chain → mkAppN" }]

meta initialize
  Check.register (α := ExprAppChainToMkAppNMatch)
