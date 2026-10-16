module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure MergeBindersWithSameType.Binder where
  stx : Syntax
  names : TSyntaxArray [`ident, ``Lean.Parser.Term.hole]
  ty : TSyntax `term

private structure MergeBindersWithSameTypeMatch where
  secondBinder : Syntax
  fullRange : Syntax
  run : Array MergeBindersWithSameType.Binder

/-- Match a `(x y … : T)` explicit binder with a type annotation and no default. -/
private meta def matchExplicitBinder? : Syntax → Option MergeBindersWithSameType.Binder
  | stx@`(bracketedBinder| ($names* : $ty)) => some { stx, names, ty }
  | _ => none

private meta def sharesType (prev next : Syntax) : Bool :=
  match matchExplicitBinder? prev, matchExplicitBinder? next with
  | some first, some second => first.ty == second.ty
  | _, _ => false

private meta def runWithSharedType? (run : List Syntax) : Option MergeBindersWithSameTypeMatch := do
  guard (run.length ≥ 2)
  let binders ← run.toArray.mapM matchExplicitBinder?
  return {
    secondBinder := (← binders[1]?).stx
    fullRange := mkNullNode (binders.map (·.stx))
    run := binders
  }

private meta instance : Check MergeBindersWithSameTypeMatch where
  name := `mergeBindersWithSameType
  kinds := #[``Command.optDeclSig, ``Command.declSig]
  severity := .information
  category := .style
  detect := fun stx => pure <|
    let binders := (stx.getArg 0).getArgs
    (binders.toList.splitBy sharesType).toArray.filterMap runWithSharedType?
  message := fun _ => m!"Merge binders with the same type"
  emphasize := fun m => m.secondBinder
  reference := some { topic := "Shared binders", url := "https://leanprover.github.io/functional_programming_in_lean/monads/conveniences.html" }
  explanation := fun _ => m!"Consecutive explicit binders with the same type can be merged into a single binder group."
  replacements := fun m => do
    let allNames := m.run.flatMap (·.names)
    let some first := m.run[0]? | return #[]
    let ty := first.ty
    let repl ← `(bracketedBinder| ($allNames* : $ty))
    return #[{
      emphasizedSyntax := m.secondBinder
      oldSyntax := m.fullRange
      newSyntax := repl
      inlineViolationLabel := m!"shared type"
      category := `bracketedBinder
    }]

meta initialize Check.register (α := MergeBindersWithSameTypeMatch)
