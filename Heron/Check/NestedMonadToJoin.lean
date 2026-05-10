module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure NestedMonadToJoinMatch where
  outerStx : Syntax
  inner : Syntax
  monadName : Name

private meta def findMatch? : Syntax → Option NestedMonadToJoinMatch
  | stx@`($fn:ident $args*) => do
    let lastArg ← args.back?
    let `(($innerApp:term)) := lastArg | none
    let `($innerFn:ident $innerArgs*) := innerApp | none
    guard (fn.getId == innerFn.getId)
    let outerLeading := args.pop
    let innerLeading := innerArgs.pop
    guard (outerLeading.size == innerLeading.size)
    guard (outerLeading.zip innerLeading |>.all fun (a, b) => a == b)
    return { outerStx := stx, inner := innerApp, monadName := fn.getId }
  | _ => none

private meta instance : Check NestedMonadToJoinMatch where
  name := `nestedMonadToJoin
  kinds := #[``Term.app]
  severity := .warning
  category := .simplification
  detect := fun stx => pure <|
    match findMatch? stx with
    | some m => #[m]
    | none => #[]
  message := fun m => m! "Nested `{m.monadName}` can be flattened with `join`"
  emphasize := fun m => m.outerStx
  tags := #[.unnecessary]
  reference := none
  explanation := fun m => m! "`{m.monadName } ({m.monadName } α)` is equivalent to `{m.monadName} α` via `join`. \
       The extra nesting layer is redundant and can be flattened."
  replacements := fun m => pure
    #[{ emphasizedSyntax := m.outerStx
        oldSyntax := m.outerStx
        newSyntax := m.inner
        inlineViolationLabel := m!"nested monad" }]

meta initialize Check.register (α := NestedMonadToJoinMatch)
