import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure NestedMonadToJoinMatch where
  outerStx : Syntax
  inner : Syntax
  monadName : String

/-- Detect `m (m α …)` patterns where the outer and inner constructor match.
For multi-arg constructors like `Except ε`, also verifies the leading args match. -/
private def findNestedMonadToJoin : Syntax → Array NestedMonadToJoinMatch :=
  Syntax.collectAll fun
    | stx@`($fn $args*) =>
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

@[check_rule]
instance : Check NestedMonadToJoinMatch where
  name := `nestedMonadToJoin
  severity := .warning
  category := .simplification
  find := findNestedMonadToJoin
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

namespace Tests

-- Nested Option in a function with multiple parameters
#assertCheck nestedMonadToJoin in
def flatten (xs : List Nat) (default : Nat) : Option (Option Nat) := sorry
becomes `(def flatten (xs : List Nat) (default : Nat) : Option Nat := sorry)

-- Nested Except with compound error type, buried in a signature with binders
#assertCheck nestedMonadToJoin in
def tryParse {α : Type} (input : String) : Except (List String) (Except (List String) α) := sorry
becomes `(def tryParse {α : Type} (input : String) : Except (List String) α := sorry)

-- Nested Option appearing in a let body type annotation
#assertCheck nestedMonadToJoin in
def g := let x : Option (Option (List Nat)) := none; x
becomes `(def g := let x : Option (List Nat) := none; x)

#assertIgnore nestedMonadToJoin in
  def h : Option Nat :=
    sorry

-- Different error types — not joinable
#assertIgnore nestedMonadToJoin in
  def k : Except String (Except Int Nat) :=
    sorry

-- Different constructors — not same-monad nesting
#assertIgnore nestedMonadToJoin in
  def l : Option (Except String Nat) :=
    sorry

-- Except with matching simple error but the arg types are complex
#assertIgnore nestedMonadToJoin in
  def m' : Except (List String) (Except (List Int) Nat) :=
    sorry

end Tests
