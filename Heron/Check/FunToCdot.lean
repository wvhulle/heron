module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure FunToCdotMatch where
  /-- The `fun x => body` node, used to anchor the diagnostic. -/
  funStx : Syntax
  /-- Node whose range is replaced: the enclosing `(…)` when the lambda is already
  parenthesised, otherwise `funStx` itself. Replacing the enclosing paren (rather than
  just the `fun`) keeps the output at a single set of parens — `(· + 1)`, not `((· + 1))`. -/
  replaceStx : Syntax
  body : Syntax
  paramName : Name

/-- Count how many times `name` appears as a replaceable bare identifier in `stx`.
Returns `none` (ineligible) when `·` could not faithfully stand in for the parameter:
- an occurrence nested inside `Term.paren` (which would change `·` scoping), or
- a projection/dotted use like `s.field` (`replaceM` only rewrites the bare `s`, so
  rewriting would leave `s.field` referencing the now-removed binder). -/
private meta partial def cdotEligibleCount (name : Name) (stx : Syntax) (insideParens := false) : Option Nat :=
  if stx.isIdent then
    if stx.getId == name then (if insideParens then none else some 1)
    else if stx.getId.getRoot == name then none  -- `s.field` etc. — not replaceable
    else some 0
  else
    match stx with
    | .node _ kind args =>
      args.foldl
        (init :=
        some 0)
        fun acc child =>
        do
        let n ← acc
        let m ← cdotEligibleCount name child (insideParens || kind == ``Term.paren)
        return n + m
    | _ => some 0

/-- Match `fun x => body` where `x` occurs exactly once and not inside parens
(so `·` keeps its scope). Returns the body and parameter name. -/
private meta def matchEligibleFun? (stx : Syntax) : Option (Syntax × Name) :=
  match stx with
  | `(fun $x:ident => $body) => match body with
    | `($_:ident) => none
    | _ => match cdotEligibleCount x.getId body with
      | some 1 => some (body, x.getId)
      | _ => none
  | _ => none

private meta instance : Check FunToCdotMatch where
  name := `funToCdot
  -- Also match `Term.paren` so a `(fun x => …)` is replaced as a unit (one set of parens).
  -- `consumesSubtree` then stops the inner `Term.fun` from re-matching and double-firing.
  kinds := #[``Term.paren, ``Term.fun]
  consumesSubtree := true
  severity := .information
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    -- Lambda already wrapped in parentheses: replace the whole `(fun x => …)`.
    | `(($inner)) => match matchEligibleFun? inner with
      | some (body, p) => #[{ funStx := inner, replaceStx := stx, body, paramName := p }]
      | none => #[]
    -- Bare lambda (e.g. `def f := fun x => …`, trailing-lambda arg): wrap it.
    | _ => match matchEligibleFun? stx with
      | some (body, p) => #[{ funStx := stx, replaceStx := stx, body, paramName := p }]
      | none => #[]
  message := fun _ => m!"Use `·` (term-level hole) instead of explicit lambda"
  emphasize := fun m => m.funStx
  reference :=
    some
      { topic := "Centered dot",
        url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ =>
    m!"Simple lambdas like `fun x => x + 1` can be written as `(· + 1)` using Lean's term-level hole syntax."
  replacements := fun m => do
    let name := m.paramName
    let newBody ← m.body.replaceM fun stx => pure (if stx.isIdent && stx.getId == name then some (mkAtom "·") else none)
    -- Wrap the `·` body in parentheses so the replacement is self-delimiting (`(· + 1)`).
    -- Without the parens, an unparenthesized lambda site (`def f := fun x => x + 1`,
    -- `xs.map fun x => x + 1`) would yield a bare `· + 1` that mis-parses / rescopes `·`.
    let body : Term := ⟨newBody⟩
    let parenthesized ← `(($body))
    return #[{
          emphasizedSyntax := m.funStx
          oldSyntax := m.replaceStx
          newSyntax := parenthesized
          inlineViolationLabel := m!"fun → ·" }]

meta initialize Check.register (α := FunToCdotMatch)
