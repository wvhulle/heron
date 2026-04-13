import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure FunToCdotMatch where
  funStx : Syntax
  body : Syntax
  paramName : Name

/-- Count how many times `name` appears as an identifier in `stx`,
returning `none` if any occurrence is nested inside `Term.paren`
(which would change `·` scoping). -/
private partial def cdotEligibleCount (name : Name) (stx : Syntax) (insideParens := false) : Option Nat :=
  if stx.isIdent && stx.getId == name then
    if insideParens then none else some 1
  else match stx with
    | .node _ kind args =>
      args.foldl (init := some 0) fun acc child => do
        let n ← acc
        let m ← cdotEligibleCount name child (insideParens || kind == ``Term.paren)
        return n + m
    | _ => some 0

private def findFunToCdot : Syntax → Array FunToCdotMatch :=
  Syntax.collectAll fun
    | stx@`(fun $x:ident => $body) =>
      if body.raw.isIdent then #[]
      else match cdotEligibleCount x.getId body with
        | some 1 => #[{ funStx := stx, body, paramName := x.getId }]
        | _ => #[]
    | _ => #[]

@[check_rule] instance : Check FunToCdotMatch where
  name := `funToCdot
  severity := .information
  category := .simplification
  find := findFunToCdot
  message := fun _ => m!"Use `·` (term-level hole) instead of explicit lambda"
  emphasize := fun m => m.funStx
  reference := some { topic := "Centered dot", url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ => m!"Simple lambdas like `fun x => x + 1` can be written as `(· + 1)` using Lean's term-level hole syntax."
  replacements := fun m => do
    let name := m.paramName
    let newBody ← m.body.replaceM fun stx =>
      pure (if stx.isIdent && stx.getId == name then some (mkAtom "·") else none)
    return #[{
      emphasizedSyntax := m.funStx
      oldSyntax := m.funStx
      newSyntax := newBody
      inlineViolationLabel := m!"fun → ·"
    }]

namespace Tests

#assertCheck funToCdot in
def f := List.map (fun x => x + 1) [1, 2, 3]
becomes `(def f := List.map (· + 1) [1, 2, 3])

#assertCheck funToCdot in
def g := List.filter (fun x => x > 0) [1, 2, 3]
becomes `(def g := List.filter (· > 0) [1, 2, 3])

-- Ignore: parameter used more than once
#assertIgnore funToCdot in
def h := List.map (fun x => x + x) [1, 2, 3]

-- Ignore: parameter inside parens (· would mis-scope)
#assertIgnore funToCdot in
def k := List.map (fun x => f (x + 1)) [1, 2, 3]

-- Ignore: multiple parameters
#assertIgnore funToCdot in
def m := List.map (fun x y => x + y) [1, 2, 3]

-- Ignore: body is just the parameter
#assertIgnore funToCdot in
def n := List.map (fun x => x) [1, 2, 3]

-- Ignore: parameter not used
#assertIgnore funToCdot in
def p := List.map (fun x => 42) [1, 2, 3]

end Tests
