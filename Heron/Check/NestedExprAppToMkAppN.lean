module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Meta Parser Heron

private structure NestedExprAppToMkAppNMatch where
  fullStx : Syntax
  fn : Term
  args : TSyntaxArray `term

/-- A single `Expr.app f a` or `.app f a` node, decomposed. -/
private structure AppNode where
  fn : Term
  arg : Term

/-- A flattened left-deep app chain: `f a₁ … aₙ`. -/
private structure AppChain where
  innermostFn : Term
  args : TSyntaxArray `term

/-- Strip one layer of parentheses, if present. -/
private meta def stripParen : Syntax → Syntax
  | `(($inner)) => inner
  | s => s

/-- Match `Expr.app f a` or `.app f a`. -/
private meta def matchApp? : Syntax → Option AppNode
  | `(Expr.app $fn $arg) => some { fn, arg }
  | `(Lean.Expr.app $fn $arg) => some { fn, arg }
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

private meta def detectExprAppChain (stx : Syntax) :
    CommandElabM (Array NestedExprAppToMkAppNMatch) := do
  let some { innermostFn, args } := collectAppChain stx | return #[]
  unless args.size >= 2 do return #[]
  unless ← elaboratesToApplicationOf stx ``Lean.Expr.app do return #[]
  return #[{ fullStx := stx, fn := innermostFn, args }]

set_option hygiene false in
private meta def mkAppNCall (fn : Term) (args : TSyntaxArray `term) : CommandElabM Term :=
  `(mkAppN $fn #[$args,*])

private meta instance : Check NestedExprAppToMkAppNMatch
    where
  name := `nestedExprAppToMkAppN
  description := "Suggests `mkAppN` instead of nested `Expr.app`."
  kinds := #[``Term.app]
  severity := .information
  category := .simplification
  detect := detectExprAppChain
  consumesSubtree := true
  message := fun _ => m!"Use `mkAppN` instead of nested `Expr.app`"
  emphasize := fun m => m.fullStx
  sources := #[.metaprogrammingInLean "Expressions" "03_expressions.html"]
  explanation := fun _ =>
    m!"Chains of `Expr.app (Expr.app f a) b` can be simplified to `mkAppN f #[a, b]`. When `f` is \
       a constant, `Lean.Meta.mkAppM` is usually better still: it fills in implicit arguments and \
       universe levels and checks the types."
  replacements := some fun m => do
    let repl ← mkAppNCall m.fn m.args
    return #[{
          emphasizedSyntax := m.fullStx
          oldSyntax := m.fullStx
          newSyntax := repl
          inlineViolationLabel := m!"Expr.app chain → mkAppN" }]

register_check NestedExprAppToMkAppNMatch
