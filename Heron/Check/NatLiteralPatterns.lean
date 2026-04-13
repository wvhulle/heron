import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private inductive NatLiteralPatternsMatch where
  /-- `Nat.zero` in a pattern position. -/
  | zero (zeroStx : Syntax)
  /-- `Nat.succ k` in a pattern position. -/
  | succ (appStx : Syntax) (arg : Syntax)

/-- Find `Nat.zero` or `Nat.succ k` idents inside a pattern. -/
private def detectNatPattern : Syntax → Array NatLiteralPatternsMatch :=
  Syntax.collectAll fun
    | stx@`($fn $arg) =>
      if fn.raw.isIdent && fn.raw.getId == `Nat.succ then #[.succ stx arg]
      else #[]
    | stx =>
      if stx.isIdent && stx.getId == `Nat.zero then #[.zero stx]
      else #[]

private def findNatLiteralPatterns : Syntax → Array NatLiteralPatternsMatch :=
  Syntax.collectAll fun
    | `(match $_:term with $alts:matchAlts) =>
      alts.raw[0]!.getArgs.flatMap fun alt => detectNatPattern alt[1]!
    | _ => #[]

@[check_rule] instance : Check NatLiteralPatternsMatch where
  name := `natLiteralPatterns
  severity := .information
  category := .style
  find := findNatLiteralPatterns
  message := fun
    | .zero .. => m!"Use `0` instead of `Nat.zero`"
    | .succ .. => m!"Use `n + 1` instead of `Nat.succ n`"
  emphasize := fun
    | .zero s => s
    | .succ s _ => s
  reference := some { topic := "Natural number patterns", url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun
    | .zero .. => m!"Pattern `Nat.zero` can be written as the numeric literal `0`."
    | .succ .. => m!"Pattern `Nat.succ n` can be written as `n + 1`."
  replacements := fun
    | .zero s => do
      let repl ← `(0)
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := repl, inlineViolationLabel := m!"Nat.zero → 0" }
      return #[r]
    | .succ s arg => do
      let argId : TSyntax `term := ⟨arg⟩
      let repl ← `($argId + 1)
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := repl, inlineViolationLabel := m!"Nat.succ → + 1" }
      return #[r]

namespace Tests

#assertCheck natLiteralPatterns in
def f (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ k => k
becomes `(def f (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => k)

-- Ignore: already using numeric patterns
#assertIgnore natLiteralPatterns in
def g (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => k

end Tests
