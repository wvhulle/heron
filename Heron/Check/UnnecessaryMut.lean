module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure UnnecessaryMutMatch where
  doLetStx : Syntax
  ident : TSyntax `ident
  valStx : TSyntax `term

/-- Match `let mut x := e`, returning the binding components. -/
private meta def matchMutLet? : Syntax → Option UnnecessaryMutMatch
  | stx@`(doElem| let mut $x:ident := $v) =>
    some { doLetStx := stx, ident := x, valStx := v }
  | _ => none

/-- Collect every `x := e` reassignment target appearing anywhere under `stx`,
including nested do blocks. -/
private meta partial def collectReassigned (stx : Syntax) : Std.HashSet Name :=
  let here : Std.HashSet Name :=
    match stx with
    | `(doElem| $x:ident := $_) => ({} : Std.HashSet Name).insert x.getId
    | _ => {}
  stx.getArgs.foldl (init := here) fun acc child => acc.union (collectReassigned child)

/-- Detect `let mut x := e` where x is never reassigned in `doSeq`. -/
private meta def detectUnnecessaryMuts (doSeq : Syntax) : Array UnnecessaryMutMatch :=
  let elems := getDoElems doSeq
  let reassigned := collectReassigned doSeq
  elems.filterMap fun elem => do
    let m ← matchMutLet? elem
    guard !(reassigned.contains m.ident.getId)
    some m

private meta instance : Check UnnecessaryMutMatch where
  name := `unnecessaryMut
  kinds := #[``Term.doSeqIndent, ``Term.doSeqBracketed]
  severity := .warning
  category := .simplification
  detect := fun stx => pure (detectUnnecessaryMuts stx)
  message := fun _ => m!"Remove unnecessary `mut`"
  emphasize := fun m => m.doLetStx
  reference := some { topic := "`let mut`", url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/do.html#mutable-variables" }
  tags := #[.unnecessary]
  explanation := fun _ => m!"This variable is declared `mut` but never reassigned. Use `let` instead of `let mut` to signal immutability."
  replacements := fun m => do
    let repl ← `(doElem| let $m.ident := $m.valStx)
    return #[{
      emphasizedSyntax := m.doLetStx
      oldSyntax := m.doLetStx
      newSyntax := repl
      category := `doElem
      inlineViolationLabel := m!"unused mut"
    }]

meta initialize Check.register (α := UnnecessaryMutMatch)
