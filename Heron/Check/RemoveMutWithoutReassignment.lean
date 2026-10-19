module

public meta import Heron.Check
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure RemoveMutWithoutReassignmentMatch where
  doLetStx : Syntax
  ident : TSyntax `ident
  valStx : TSyntax `term

/-- Match `let mut x := e`, returning the binding components. -/
private meta def matchMutLet? : Syntax → Option RemoveMutWithoutReassignmentMatch
  | stx@`(doElem| let mut $x:ident := $v) =>
    some { doLetStx := stx, ident := x, valStx := v }
  | _ => none

private meta partial def patternIdents (pat : Syntax) : Std.HashSet Name :=
  let here : Std.HashSet Name := if pat.isIdent then ({} : Std.HashSet Name).insert pat.getId else {}
  pat.getArgs.foldl (init := here) fun acc child => acc.union (patternIdents child)

private meta def reassignedHere : Syntax → Std.HashSet Name
  | `(doElem| $x:ident := $_) => patternIdents x
  | `(doElem| $x:ident ← $_) => patternIdents x
  | `(doElem| $pat:term := $_) => patternIdents pat
  | `(doElem| $pat:term ← $_) => patternIdents pat
  | _ => {}

/-- Collect every reassignment target appearing anywhere under `stx`,
including nested do blocks. -/
private meta partial def collectReassigned (stx : Syntax) : Std.HashSet Name :=
  let here := reassignedHere stx
  stx.getArgs.foldl (init := here) fun acc child => acc.union (collectReassigned child)

/-- Detect `let mut x := e` where x is never reassigned in `doSeq`. -/
private meta def detectUnnecessaryMuts (doSeq : Syntax) : Array RemoveMutWithoutReassignmentMatch :=
  let elems := getDoElems doSeq
  let reassigned := collectReassigned doSeq
  elems.filterMap fun elem => do
    let m ← matchMutLet? elem
    guard !(reassigned.contains m.ident.getId)
    some m

private meta instance : Check RemoveMutWithoutReassignmentMatch where
  name := `removeMutWithoutReassignment
  kinds := #[``Term.doSeqIndent, ``Term.doSeqBracketed]
  severity := .warning
  category := .simplification
  detect := fun stx => pure (detectUnnecessaryMuts stx)
  message := fun _ => m!"Remove unnecessary `mut`"
  emphasize := fun m => m.doLetStx
  sources := #[.functionalProgrammingInLean "`let mut`" "Monad-Transformers/More-do-Features/#let-mut"]
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

meta initialize Check.register (α := RemoveMutWithoutReassignmentMatch)
