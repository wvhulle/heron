module

public meta import Heron.Check
meta import Heron.Register

set_option linter.syntheticSyntaxConstruction false

open Lean Elab Command Meta Parser Heron

private structure NestedExprAppToMkAppNMatch where
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
  | `(Lean.Expr.app $fn $arg) => some { fn, arg }
  | `(.app $fn $arg) => some { fn, arg }
  | _ => none

private meta def namesExprApp : Syntax → Bool
  | `(Expr.app $_ $_) => true
  | `(Lean.Expr.app $_ $_) => true
  | _ => false

private meta def isExprTyped (e : Expr) : MetaM Bool := do
  return (← whnfR (← instantiateMVars (← inferType e))).isConstOf ``Lean.Expr

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
  unless namesExprApp stx do
    let some true ← runMetaMForSyntax stx isExprTyped | return #[]
  return #[{ fullStx := stx, fn := innermostFn, args }]

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
    let fn : TSyntax `term := ⟨m.fn⟩
    let args : TSyntaxArray `term := m.args.map (⟨·⟩)
    let mkAppNId := mkIdent `mkAppN
    let repl ← `($mkAppNId $fn #[$args,*])
    return #[{
          emphasizedSyntax := m.fullStx
          oldSyntax := m.fullStx
          newSyntax := repl
          inlineViolationLabel := m!"Expr.app chain → mkAppN" }]

register_check NestedExprAppToMkAppNMatch
