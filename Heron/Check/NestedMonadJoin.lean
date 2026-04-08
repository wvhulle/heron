import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure NestedMonadJoinMatch where
  outerStx : Syntax
  inner : Syntax
  monadName : String

/-- Extract the function name from a syntax node if it's a simple identifier application. -/
private def appFnName? (stx : Syntax) : Option String :=
  if stx.getKind == ``Term.app then
    let fn := stx[0]!
    if fn.isIdent then some (reprintTrimmed fn) else none
  else none

/-- Extract arguments from an application syntax node. -/
private def appArgs (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Term.app then stx[1]!.getArgs else #[]

/-- Unwrap parentheses from a syntax node, returning the inner node. -/
private def unwrapParen? (stx : Syntax) : Option Syntax :=
  if stx.getKind == ``Term.paren then some stx[1]! else none

/-- Check whether leading args (before the last) match textually between outer and inner. -/
private def leadingArgsMatch (outerArgs innerArgs : Array Syntax) : Bool :=
  let outerLeading := outerArgs.pop
  let innerLeading := innerArgs.pop
  outerLeading.size == innerLeading.size &&
    (outerLeading.zip innerLeading |>.all fun (a, b) => reprintTrimmed a == reprintTrimmed b)

/-- Detect `m (m α …)` patterns where the outer and inner constructor match.
For multi-arg constructors like `Except ε`, also verifies the leading args match. -/
private def findNestedMonadJoin : Syntax → Array NestedMonadJoinMatch :=
  Syntax.collectAll fun stx =>
    match appFnName? stx with
    | none => #[]
    | some outerName =>
      let outerArgs := appArgs stx
      if outerArgs.size == 0 then #[]
      else
        let lastArg := outerArgs[outerArgs.size - 1]!
        match unwrapParen? lastArg with
        | none => #[]
        | some inner =>
          match appFnName? inner with
          | none => #[]
          | some innerName =>
            if outerName != innerName then #[]
            else
              let innerArgs := appArgs inner
              if !leadingArgsMatch outerArgs innerArgs then #[]
              else
                -- The replacement is just the inner application (removing one nesting layer)
                -- e.g. Option (Option Nat) → the inner is `Option Nat`
                -- e.g. Except String (Except String Nat) → the inner is `Except String Nat`
                #[{ outerStx := stx, inner, monadName := outerName }]

@[check_rule]
instance : Check NestedMonadJoinMatch where
  ruleName := `nestedMonadJoin
  severity := .warning
  category := .simplification
  pureDetect := findNestedMonadJoin
  message := fun m => m! "Nested `{m.monadName}` can be flattened with `join`"
  node := fun m => m.outerStx
  tags := #[.unnecessary]
  reference := some { topic := "Monad join", url := "https://lean-lang.org/lean4/doc/monads/transformers.html" }
  explanation := fun m => m! "`{m.monadName } ({m.monadName } α)` is equivalent to `{m.monadName} α` via `join`. \
       The extra nesting layer is redundant and can be flattened."
  replacements := fun m => pure
    #[{ sourceNode := m.outerStx
        targetNode := m.outerStx
        insertText := m.inner
        sourceLabel := m!"nested monad" }]

namespace Tests

-- Nested Option in a function with multiple parameters
#assertCheck nestedMonadJoin in
def flatten (xs : List Nat) (default : Nat) : Option (Option Nat) := sorry
becomes `(def flatten (xs : List Nat) (default : Nat) : Option Nat := sorry)

-- Nested Except with compound error type, buried in a signature with binders
#assertCheck nestedMonadJoin in
def tryParse {α : Type} (input : String) : Except (List String) (Except (List String) α) := sorry
becomes `(def tryParse {α : Type} (input : String) : Except (List String) α := sorry)

-- Nested Option appearing in a let body type annotation
#assertCheck nestedMonadJoin in
def g := let x : Option (Option (List Nat)) := none; x
becomes `(def g := let x : Option (List Nat) := none; x)

#assertIgnore nestedMonadJoin in
  def h : Option Nat :=
    sorry

-- Different error types — not joinable
#assertIgnore nestedMonadJoin in
  def k : Except String (Except Int Nat) :=
    sorry

-- Different constructors — not same-monad nesting
#assertIgnore nestedMonadJoin in
  def l : Option (Except String Nat) :=
    sorry

-- Except with matching simple error but the arg types are complex
#assertIgnore nestedMonadJoin in
  def m' : Except (List String) (Except (List Int) Nat) :=
    sorry

end Tests
