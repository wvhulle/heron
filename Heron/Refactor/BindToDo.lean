module

public meta import Heron.Refactor

open Lean Elab Command Parser Heron

private structure Binding where
  lhs : TSyntax `term
  ident : TSyntax `ident

private structure BindToDoMatch where
  fullStx : Syntax
  bindings : Array Binding
  finalBody : TSyntax `term
  deriving Nonempty

/-- Match `lhs >>= fun x => body`, splitting off the leading binding from the
remaining body. -/
private meta def matchBind? : TSyntax `term → Option (Binding × TSyntax `term)
  | `($lhs >>= fun $x:ident => $body) => some ({ lhs, ident := x }, body)
  | _ => none

/-- Walk a chain of `>>= fun x => …` bindings into a flat match. -/
private meta partial def collectBindChain (fullStx : Syntax) (stx : TSyntax `term) :
    BindToDoMatch :=
  match matchBind? stx with
  | none => { fullStx, bindings := #[], finalBody := stx }
  | some (b, body) =>
    let rest := collectBindChain fullStx body
    { rest with bindings := #[b] ++ rest.bindings }

private meta instance : Refactor BindToDoMatch where
  name := `bindToDo
  kinds := #[`«term_>>=_»]
  detect := fun stx => pure <|
    let m := collectBindChain stx ⟨stx⟩
    if m.bindings.isEmpty then #[] else #[m]
  consumesSubtree := true
  message := fun _ => m!"Convert `>>=` to do-notation"
  replacements := fun m => do
    let lets ← m.bindings.mapM fun b =>
      `(Parser.Term.doSeqItem| let $b.ident ← $b.lhs:term)
    let body ← `(Parser.Term.doSeqItem| $m.finalBody:term)
    let seq ← `(Parser.Term.doSeq| $(lets.push body)*)
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
