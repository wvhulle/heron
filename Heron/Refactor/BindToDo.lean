import Heron.Refactor
import Heron.Assert

open Lean Elab Command Parser Heron

private structure BindToDoMatch where
  fullStx : Syntax
  replacement : String

/-- Try to decompose `lhs >>= fun x => body` into `(lhs, varName, body)`. -/
private def decomposeBind? (stx : Syntax) : Option (Syntax × String × Syntax) :=
  if stx.getKind != `«term_>>=_» then none
  else
    let lhs := stx[0]!
    let rhs := stx[2]!
    if rhs.getKind != ``Term.fun then none
    else
      let basicFun := rhs[1]!
      if basicFun.getKind != ``Term.basicFun then none
      else
        let params := basicFun[0]!
        if params.getNumArgs != 1 then none
        else
          let varName := reprintTrimmed params[0]!
          let body := basicFun[3]!
          some (lhs, varName, body)

/-- Collect a chain of `>>= fun x => ...` bindings. -/
private partial def collectBindChain (stx : Syntax) : Array (Syntax × String) × Syntax :=
  match decomposeBind? stx with
  | none => (#[], stx)
  | some (lhs, varName, body) =>
    let (rest, finalBody) := collectBindChain body
    (#[(lhs, varName)] ++ rest, finalBody)

/-- Walk the syntax tree, matching outermost `>>=` chains only.
After matching a chain, skip its children to avoid duplicate inner matches. -/
private partial def findBindToDoAux (stx : Syntax) : Array BindToDoMatch :=
  match decomposeBind? stx with
  | some _ =>
    let (bindings, finalBody) := collectBindChain stx
    if bindings.isEmpty then stx.getArgs.flatMap findBindToDoAux
    else
      let letLines := bindings.map fun (lhs, varName) =>
        s!"  let {varName} ← {reprintTrimmed lhs}"
      let bodyLine := s!"  {reprintTrimmed finalBody}"
      let lines := #["do"] ++ letLines ++ #[bodyLine]
      let repl := "\n".intercalate lines.toList
      -- Only recurse into the LHS expressions, not the consumed chain body
      let lhsResults := bindings.flatMap fun (lhs, _) => findBindToDoAux lhs
      let bodyResults := findBindToDoAux finalBody
      #[{ fullStx := stx, replacement := repl }] ++ lhsResults ++ bodyResults
  | none => stx.getArgs.flatMap findBindToDoAux

@[refactor_rule] instance : Refactor BindToDoMatch where
  ruleName := `bindToDo
  detect := fun stx => return findBindToDoAux stx
  message := fun _ => m!"Convert `>>=` to do-notation"
  replacements := fun m => #[{
    sourceNode := m.fullStx
    targetNode := m.fullStx
    insertText := m.replacement
    sourceLabel := m!"bind to do"
  }]
  codeActionKind := "refactor.rewrite"

namespace Tests

#assertRefactor bindToDo in
def f := IO.getLine >>= fun s => IO.println s
becomes `(command| def f := do
  let s ← IO.getLine
  IO.println s)

#assertRefactor bindToDo in
def g := IO.getLine >>= fun s => IO.getLine >>= fun t => IO.println (s ++ t)
becomes `(command| def g := do
  let s ← IO.getLine
  let t ← IO.getLine
  IO.println (s ++ t))

#assertIgnore bindToDo in
def h := [1, 2, 3].bind (fun x => [x, x])

end Tests
