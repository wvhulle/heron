module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Meta Parser Heron

private inductive Operand where
  | literal
  | interpolated
  | value

private structure StringConcatenationToInterpolationMatch where
  concatenation : Syntax

private meta partial def appendOperands : Syntax → Array Syntax
  | `($lhs ++ $rhs) => appendOperands lhs ++ appendOperands rhs
  | operand => #[operand]

private meta def hasStringType (e : Expr) : MetaM Bool := do
  return (← whnfR (← instantiateMVars (← inferType e))).isConstOf ``String

private meta def classifyOperand (operand : Syntax) : CommandElabM (Option Operand) := do
  match operand with
  | `($_:str) => return some .literal
  | `(toString $_) => return some .value
  | `(s!$_) => return some .interpolated
  | _ =>
    let isString := (← runMetaMForEachExactSyntax operand hasStringType).any id
    return if isString then some .value else none

private meta def isLiteral : Operand → Bool
  | .literal => true
  | _ => false

private meta def detectStringConcatenation (stx : Syntax) :
    CommandElabM (Array StringConcatenationToInterpolationMatch) := do
  let some operands ← (appendOperands stx).mapM classifyOperand <&> (·.mapM id) | return #[]
  unless operands.any isLiteral && operands.any (!isLiteral ·) do return #[]
  return #[{ concatenation := stx }]

private meta instance : Check StringConcatenationToInterpolationMatch where
  name := `stringConcatenationToInterpolation
  description := "Flags `\"…\" ++ toString x ++ \"…\"` and suggests an interpolated `s!\"…{x}…\"` string instead."
  kinds := #[``«term_++_»]
  consumesSubtree := true
  severity := .information
  category := .style
  detect := detectStringConcatenation
  message := fun _ => m!"Use string interpolation `s!\"…\"` instead of concatenating with `++`"
  emphasize := fun m => m.concatenation
  sources := #[.functionalProgrammingInLean "String interpolation"
    "Getting-to-Know-Lean/Additional-Conveniences/#string-interpolation"]
  explanation := fun _ =>
    m!"Prefixing a string with `s!` replaces each `\{e}` with `toString e`, like f-strings in \
       Python or `$\"…\"` strings in C#. For example, `\"Hello, \" ++ name ++ \"!\"` can be \
       written `s!\"Hello, \{name}!\"`, and `\"n = \" ++ toString n` as `s!\"n = \{n}\"`. It \
       avoids the explicit `toString` calls and keeps the text readable in one piece."

register_check StringConcatenationToInterpolationMatch
