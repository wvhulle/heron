module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure OptionWrapFilterMatch where
  fullStx : TSyntax `term
  value : TSyntax `term
  predicate : TSyntax `term

private meta instance : Check OptionWrapFilterMatch where
  name := `optionWrapFilter
  kinds := #[``Term.pipeProj, ``Term.app]
  severity := .information
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | `(some $value |>.filter $predicate) => #[{ fullStx := ⟨stx⟩, value, predicate }]
    | `((some $value).filter $predicate) => #[{ fullStx := ⟨stx⟩, value, predicate }]
    | _ => #[]
  message := fun _ => m!"Replace `some _ |>.filter _` with a `guard` in an `Option` `do`-block"
  emphasize := fun m => m.fullStx
  reference := none
  explanation := fun _ =>
    m!"`some x |>.filter p` is `if p x then some x else none`. Inside an `Option` `do`-block, \
       this is more directly expressed as `do guard (p x); return x`, making the predicate's \
       short-circuit role explicit."
  replacements := fun m => do
    let guardId := mkIdent `guard
    let guardCall ← `($guardId ($m.predicate $m.value))
    let guardItem ← `(Parser.Term.doSeqItem| $guardCall:term)
    let returnItem ← `(Parser.Term.doSeqItem| return $m.value)
    let seq ← `(Parser.Term.doSeq| $(#[guardItem, returnItem])*)
    let repl ← `(do $seq)
    return #[{
      emphasizedSyntax := m.fullStx
      oldSyntax := m.fullStx
      newSyntax := repl
      inlineViolationLabel := m!"some + filter → guard"
    }]

meta initialize Check.register (α := OptionWrapFilterMatch)
