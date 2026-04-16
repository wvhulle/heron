import Heron.Check

open Lean Elab Command Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure MergeIntrosMatch where
  secondIntro : Syntax
  fullRange : Syntax
  allIntros : Array Syntax

private def collectIntroTactics : Syntax → Array Syntax :=
  Syntax.collectAll fun stx => if stx.getKind == ``Lean.Parser.Tactic.intro then #[stx] else #[]

private def introIdents : Syntax → Array Syntax :=
  Syntax.collectAll fun stx => if stx.isIdent || stx.getKind == ``Lean.Parser.Term.hole then #[stx] else #[]

private def detectIntros (stx : Syntax) : Array MergeIntrosMatch :=
  let intros := collectIntroTactics stx
  if intros.size ≤ 1 then #[]
  else
    match mkSpan intros[0]! intros[intros.size - 1]! with
    | some fullRange => #[{ secondIntro := intros[1]!, fullRange, allIntros := intros }]
    | none => #[]

@[check_rule]
instance : Check MergeIntrosMatch where
  name := `mergeIntros
  severity := .warning
  category := .simplification
  find := detectIntros
  message := fun _ => m!"Merge intros"
  emphasize := fun m => m.secondIntro
  tags := #[.unnecessary]
  explanation := fun _ =>
    m!"Multiple sequential `intro` tactics can be merged into one. This reduces tactic noise and is idiomatic Lean style."
  replacements := fun m => do
    let names : TSyntaxArray `ident := (m.allIntros.flatMap introIdents).map (⟨·⟩)
    let repl ← `(tactic| intro $names*)
    return #[{
          emphasizedSyntax := m.secondIntro
          oldSyntax := m.fullRange
          newSyntax := repl
          category := `tactic
          inlineViolationLabel := m!"sequential intro" }]
