module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private inductive NatConstructorPatternsToLiteralsMatch where
  /-- `Nat.zero` in a pattern position. -/
  | zero (zeroStx : Syntax)
  /-- `Nat.succ (… (Nat.succ base))` with `succCount` applications in a pattern position. -/
  | succ (appStx : Syntax) (base : Syntax) (succCount : Nat) (needsParens : Bool)

private meta def unwrapParens : Syntax → Syntax
  | `(($inner)) => inner
  | stx => stx

private meta partial def peelSuccs (stx : Syntax) (succCount : Nat := 0) : Syntax × Nat :=
  match stx with
  | `(Nat.succ $arg) => peelSuccs (unwrapParens arg) (succCount + 1)
  | _ => (stx, succCount)

private meta def delimitsOperand (kind : SyntaxNodeKind) : Bool :=
  kind == ``Term.paren || kind == ``Term.tuple || kind == ``Term.anonymousCtor

/-- Find `Nat.zero` or `Nat.succ k` idents inside a pattern subtree. A chain of
`Nat.succ` is reported once, at its outermost application. -/
private meta partial def detectNatPattern (stx : Syntax) (needsParens := false) :
    Array NatConstructorPatternsToLiteralsMatch :=
  match stx with
  | `(Nat.succ $_) =>
    let (base, succCount) := peelSuccs stx
    #[.succ stx base succCount needsParens] ++ (base.getArgs.flatMap (detectNatPattern · true))
  | `(Nat.zero) => #[.zero stx]
  | _ => stx.getArgs.flatMap (detectNatPattern · !(delimitsOperand stx.getKind))

private meta instance : Check NatConstructorPatternsToLiteralsMatch where
  name := `natConstructorPatternsToLiterals
  kinds := #[``Term.match]
  severity := .information
  category := .style
  detect := fun stx => pure <|
    match stx with
    | `(match $_:term with $alts:matchAlt*) =>
      alts.flatMap fun
        | `(Term.matchAltExpr| | $pats,* => $_) =>
          pats.getElems.flatMap fun pat => detectNatPattern pat
        | _ => #[]
    | _ => #[]
  message := fun
    | .zero .. => m!"Use `0` instead of `Nat.zero`"
    | .succ .. => m!"Use `n + 1` instead of `Nat.succ n`"
  emphasize := fun
    | .zero s => s
    | .succ s .. => s
  reference := some { topic := "Natural number patterns", url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun
    | .zero .. => m!"Pattern `Nat.zero` can be written as the numeric literal `0`."
    | .succ .. => m!"Pattern `Nat.succ n` can be written as `n + 1`, and nested `Nat.succ` applications as `n + k`."
  replacements := fun
    | .zero s => do
      let repl ← `(0)
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := repl, inlineViolationLabel := m!"Nat.zero → 0" }
      return #[r]
    | .succ s base succCount needsParens => do
      let offset ← `($(Syntax.mkNumLit (toString succCount)):num)
      let sum ← match base with
        | `(Nat.zero) => pure offset
        | _ => `($(⟨base⟩) + $offset)
      let repl ← if needsParens then `(($sum)) else pure sum
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := repl, inlineViolationLabel := m!"Nat.succ → + 1" }
      return #[r]

meta initialize Check.register (α := NatConstructorPatternsToLiteralsMatch)
