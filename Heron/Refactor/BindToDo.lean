module

public meta import Heron.Refactor

open Lean Elab Command Parser Heron

private structure BindToDoMatch where
  fullStx : Syntax
  bindings : Array (Syntax × Syntax)
  finalBody : Syntax

/-- Try to decompose `lhs >>= fun x => body` into `(lhs, varName, body)`. -/
private meta def decomposeBind? (stx : Syntax) : Option (Syntax × Syntax × Syntax) :=
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
          let varName := params[0]!
          let body := basicFun[3]!
          some (lhs, varName, body)

/-- Collect a chain of `>>= fun x => ...` bindings. -/
private meta partial def collectBindChain (stx : Syntax) : Array (Syntax × Syntax) × Syntax :=
  match decomposeBind? stx with
  | none => (#[], stx)
  | some (lhs, varName, body) =>
    let (rest, finalBody) := collectBindChain body
    (#[(lhs, varName)] ++ rest, finalBody)

private meta instance : Refactor BindToDoMatch where
  name := `bindToDo
  kinds := #[`«term_>>=_»]
  detect := fun stx => pure <|
    match decomposeBind? stx with
    | some _ =>
      let (bindings, finalBody) := collectBindChain stx
      if bindings.isEmpty then #[] else #[{ fullStx := stx, bindings, finalBody }]
    | none => #[]
  postProcess := Rule.dedupContainedRanges (fun m => m.fullStx.getRange?)
  message := fun _ => m!"Convert `>>=` to do-notation"
  replacements := fun m => do
    -- Build doSeqItems: one `let v ← lhs` per binding, then final body
    let mut items : Array (TSyntax ``Parser.Term.doSeqItem) := #[]
    for (lhs, varName) in m.bindings do
      let v : TSyntax `ident := ⟨varName⟩
      let l : TSyntax `term := ⟨lhs⟩
      let item ← `(Parser.Term.doSeqItem| let $v ← $l:term)
      items := items.push item
    let bodyItem ← `(Parser.Term.doSeqItem| $( (⟨m.finalBody⟩ : TSyntax `term) ):term)
    items := items.push bodyItem
    let seq ← `(Parser.Term.doSeq| $items*)
    let repl ← `(do $seq)
    return #[{
      emphasizedSyntax := m.fullStx
      oldSyntax := m.fullStx
      newSyntax := repl
      inlineViolationLabel := m!"bind to do"
    }]
  codeActionKind := "refactor.rewrite"

@[code_action_provider]
public meta def bindToDoProvider := Refactor.toCodeActionProvider (α := BindToDoMatch)

meta initialize Refactor.register (α := BindToDoMatch)
