module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private inductive NatConstructorsToLiteralsMatch where
  | zero (zeroStx : Syntax)
  | succ (appStx : Syntax) (replacement : Term)
  | unappliedSucc (succStx : Syntax)

private meta def unwrapParens : Term → Term
  | `(($inner)) => inner
  | stx => stx

private meta def refersTo (stx : Syntax) (constName : Name) : CommandElabM Bool := do
  let results ← runMetaMForEachExactSyntax stx fun e => return (← instantiateMVars e).isConstOf constName
  return results.any id

private meta def succArgument? (stx : Syntax) : CommandElabM (Option Term) := do
  let `($f:ident $arg) := stx | return none
  unless ← refersTo f ``Nat.succ do return none
  return some (unwrapParens arg)

private meta partial def peelSuccs (arg : Term) (succCount : Nat) : CommandElabM (Term × Nat) := do
  match ← succArgument? arg with
  | some inner => peelSuccs inner (succCount + 1)
  | none => return (arg, succCount)

private meta def literalFor (base : Term) (succCount : Nat) : CommandElabM Term := do
  if ← refersTo base ``Nat.zero then return quote succCount
  if let `($n:num) := base then return quote (n.getNat + succCount)
  `($base + $(quote succCount))

private meta def succReplacement (appStx : Syntax) (arg : Term) : CommandElabM Term := do
  let (base, succCount) ← peelSuccs arg 1
  let literal ← literalFor base succCount
  if ← needsParenthesesAt appStx literal then `(($literal)) else return literal

private meta def detectNatConstructor? (stx : Syntax) : CommandElabM (Option NatConstructorsToLiteralsMatch) := do
  if let some arg ← succArgument? stx then
    return some (.succ stx (← succReplacement stx arg))
  let `($x:ident) := stx | return none
  if ← refersTo x ``Nat.zero then return some (.zero stx)
  if ← refersTo x ``Nat.succ then return some (.unappliedSucc stx)
  return none

private meta def detectNatConstructors (stx : Syntax) : CommandElabM (Array NatConstructorsToLiteralsMatch) := do
  let some m ← detectNatConstructor? stx | return #[]
  if ← declaresTheorem stx then return #[]
  return #[m]

private meta instance : Check NatConstructorsToLiteralsMatch where
  name := `natConstructorsToLiterals
  description := "Suggests `0`, `n + k` and `(· + 1)` instead of `Nat.zero` and `Nat.succ`."
  kinds := #[``Term.app, identKind]
  consumesSubtree := true
  severity := .information
  category := .style
  detect := detectNatConstructors
  message := fun
    | .zero .. => m!"Use `0` instead of `Nat.zero`"
    | .succ .. => m!"Use `n + 1` instead of `Nat.succ n`"
    | .unappliedSucc .. => m!"Use `(· + 1)` instead of `Nat.succ`"
  emphasize := fun
    | .zero s => s
    | .succ s .. => s
    | .unappliedSucc s => s
  sources := #[.functionalProgrammingInLean "Natural number patterns"
    "Getting-to-Know-Lean/Additional-Conveniences/#natural-number-patterns"]
  explanation := fun
    | .zero .. => m!"`Nat.zero` can be written as the numeric literal `0`, both in patterns and in expressions."
    | .succ .. => m!"`Nat.succ n` can be written as `n + 1`, and nested `Nat.succ` applications as `n + k`. \
                     In a pattern, Lean turns `n + k` back into `Nat.succ` applications, so both forms \
                     match the same values."
    | .unappliedSucc .. => m!"`Nat.succ` used as a function is the same as `(· + 1)`."
  replacements := some fun
    | .zero s => do
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := ← `(0), inlineViolationLabel := m!"Nat.zero → 0" }
      return #[r]
    | .succ s replacement => do
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := replacement, inlineViolationLabel := m!"Nat.succ → + 1" }
      return #[r]
    | .unappliedSucc s => do
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := ← `((· + 1)), inlineViolationLabel := m!"Nat.succ → (· + 1)" }
      return #[r]

register_check NatConstructorsToLiteralsMatch
