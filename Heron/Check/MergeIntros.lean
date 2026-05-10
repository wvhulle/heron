module

public meta import Heron.Check

open Lean Elab Command Heron

private structure MergeIntrosMatch where
  secondIntro : TSyntax `tactic
  fullRange : Syntax
  allIntros : Array (TSyntax `tactic)

private meta partial def introIdents : Syntax → Array Syntax := fun stx =>
  let here := if stx.isIdent || stx.getKind == ``Lean.Parser.Term.hole then #[stx] else #[]
  here ++ stx.getArgs.flatMap introIdents

private meta def isIntro : TSyntax `tactic → Bool
  | `(tactic| intro $_*) => true
  | _ => false

/-- Pull out the tactic list of a `tacticSeq1Indented` or `tacticSeqBracketed`
node. -/
private meta def tacticSeqArgs? : Syntax → Option (Array (TSyntax `tactic))
  | `(Lean.Parser.Tactic.tacticSeq1Indented| $args:tactic*) => some args.getElems
  | `(Lean.Parser.Tactic.tacticSeqBracketed| { $args:tactic* }) => some args.getElems
  | _ => none

private meta def asMatch? (group : List (TSyntax `tactic)) : Option MergeIntrosMatch := do
  guard (group.length ≥ 2 ∧ group.all isIntro)
  let arr := group.toArray
  return { secondIntro := arr[1]!, fullRange := mkNullNode (arr.map (·.raw)), allIntros := arr }

private meta def detectIntrosAt (stx : Syntax) : Array MergeIntrosMatch :=
  tacticSeqArgs? stx
    |>.getD #[]
    |>.toList
    |>.splitBy (fun a b => isIntro a == isIntro b)
    |>.filterMap asMatch?
    |>.toArray

private meta instance : Check MergeIntrosMatch where
  name := `mergeIntros
  kinds := #[``Lean.Parser.Tactic.tacticSeq1Indented, ``Lean.Parser.Tactic.tacticSeqBracketed]
  severity := .warning
  category := .simplification
  detect := fun stx => pure (detectIntrosAt stx)
  message := fun _ => m!"Merge intros"
  emphasize := fun m => m.secondIntro
  tags := #[.unnecessary]
  explanation := fun _ =>
    m!"Multiple sequential `intro` tactics can be merged into one. This reduces tactic noise and is idiomatic Lean style."
  replacements := fun m => do
    let names : TSyntaxArray `ident :=
      (m.allIntros.flatMap fun t => introIdents t).map (⟨·⟩)
    let repl ← `(tactic| intro $names*)
    return #[{
          emphasizedSyntax := m.secondIntro
          oldSyntax := m.fullRange
          newSyntax := repl
          category := `tactic
          inlineViolationLabel := m!"sequential intro" }]

meta initialize Check.register (α := MergeIntrosMatch)
