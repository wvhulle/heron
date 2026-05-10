module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure MergeBinders.Binder where
  stx : Syntax
  names : TSyntaxArray [`ident, ``Lean.Parser.Term.hole]
  ty : TSyntax `term

private structure MergeBindersMatch where
  secondBinder : Syntax
  fullRange : Syntax
  first : MergeBinders.Binder
  second : MergeBinders.Binder

/-- Match a `(x y … : T)` explicit binder with a type annotation and no default. -/
private meta def matchExplicitBinder? : Syntax → Option MergeBinders.Binder
  | stx@`(bracketedBinder| ($names* : $ty)) => some { stx, names, ty }
  | _ => none

private meta def pairWithSharedType? (prev next : Syntax) : Option MergeBindersMatch := do
  let first ← matchExplicitBinder? prev
  let second ← matchExplicitBinder? next
  guard (first.ty == second.ty)
  return {
    secondBinder := next
    fullRange := mkNullNode #[prev, next]
    first
    second
  }

private meta instance : Check MergeBindersMatch where
  name := `mergeBinders
  kinds := #[``Command.optDeclSig, ``Command.declSig]
  severity := .information
  category := .style
  detect := fun stx => pure <|
    let binders := (stx.getArg 0).getArgs
    let pairs := (List.range (binders.size.pred)).map fun i => (binders[i]!, binders[i+1]!)
    pairs.toArray.filterMap fun (a, b) => pairWithSharedType? a b
  message := fun _ => m!"Merge binders with the same type"
  emphasize := fun m => m.secondBinder
  reference := some { topic := "Shared binders", url := "https://leanprover.github.io/functional_programming_in_lean/monads/conveniences.html" }
  explanation := fun _ => m!"Consecutive explicit binders with the same type can be merged into a single binder group."
  replacements := fun m => do
    let allNames := m.first.names ++ m.second.names
    let ty := m.first.ty
    let repl ← `(bracketedBinder| ($allNames* : $ty))
    return #[{
      emphasizedSyntax := m.secondBinder
      oldSyntax := m.fullRange
      newSyntax := repl
      inlineViolationLabel := m!"shared type"
      category := `bracketedBinder
    }]

meta initialize Check.register (α := MergeBindersMatch)
