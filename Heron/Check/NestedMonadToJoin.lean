module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure NestedMonadToJoinMatch where
  outerStx : Syntax
  inner : Syntax
  monadName : String

private meta instance : Check NestedMonadToJoinMatch where
  name := `nestedMonadToJoin
  kinds := #[``Term.app]
  severity := .warning
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | `($fn $args*) =>
      if !fn.raw.isIdent || args.size == 0 then #[]
      else
        let outerName := reprintTrimmed fn
        match args.back! with
        | `(($innerFn $innerArgs*)) =>
          if reprintTrimmed innerFn != outerName then #[]
          else
            let outerLeading := args.pop
            let innerLeading := innerArgs.pop
            if outerLeading.size != innerLeading.size then #[]
            else if !(outerLeading.zip innerLeading |>.all fun (a, b) =>
              reprintTrimmed a.raw == reprintTrimmed b.raw) then #[]
            else
              let inner : Syntax := (args.back!.raw)[1]!
              #[{ outerStx := stx, inner, monadName := outerName }]
        | _ => #[]
    | _ => #[]
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
