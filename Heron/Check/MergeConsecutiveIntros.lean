module

public meta import Heron.Check

open Lean Elab Command Heron

private structure MergeConsecutiveIntrosMatch where
  secondIntro : TSyntax `tactic
  fullRange : Syntax
  allIntros : Array (TSyntax `tactic)

private meta def isNameOrHole : TSyntax `term → Bool
  | `($_:ident) => true
  | `(_) => true
  | _ => false

private meta def plainIntroNames? : TSyntax `tactic → Option (TSyntaxArray `term)
  | `(tactic| intro $names*) =>
    if !names.isEmpty && names.all isNameOrHole then some names else none
  | _ => none

private meta def isIntro (tac : TSyntax `tactic) : Bool :=
  (plainIntroNames? tac).isSome

/-- Pull out the tactic list of a `tacticSeq1Indented` or `tacticSeqBracketed`
node. -/
private meta def tacticSeqArgs? : Syntax → Option (Array (TSyntax `tactic))
  | `(Lean.Parser.Tactic.tacticSeq1Indented| $args:tactic*) => some args.getElems
  | `(Lean.Parser.Tactic.tacticSeqBracketed| { $args:tactic* }) => some args.getElems
  | _ => none

private meta def asMatch? (group : List (TSyntax `tactic)) : Option MergeConsecutiveIntrosMatch := do
  guard (group.length ≥ 2 ∧ group.all isIntro)
  let arr := group.toArray
  return { secondIntro := arr[1]!, fullRange := mkNullNode (arr.map (·.raw)), allIntros := arr }

private meta def detectIntrosAt (stx : Syntax) : Array MergeConsecutiveIntrosMatch :=
  tacticSeqArgs? stx
    |>.getD #[]
    |>.toList
    |>.splitBy (fun a b => isIntro a == isIntro b)
    |>.filterMap asMatch?
    |>.toArray

private meta instance : Check MergeConsecutiveIntrosMatch where
  name := `mergeConsecutiveIntros
  kinds := #[``Lean.Parser.Tactic.tacticSeq1Indented, ``Lean.Parser.Tactic.tacticSeqBracketed]
  severity := .information
  category := .simplification
  detect := fun stx => pure (detectIntrosAt stx)
  message := fun _ => m!"Merge intros"
  emphasize := fun m => m.secondIntro
  tags := #[.unnecessary]
  explanation := fun _ =>
    m!"Sequential `intro` tactics that each name one or more hypotheses can be merged into a single `intro`. This reduces tactic noise and is idiomatic Lean style."
  replacements := fun m => do
    let names := m.allIntros.flatMap fun t => (plainIntroNames? t).getD #[]
    let repl ← `(tactic| intro $names*)
    return #[{
          emphasizedSyntax := m.secondIntro
          oldSyntax := m.fullRange
          newSyntax := repl
          category := `tactic
          inlineViolationLabel := m!"sequential intro" }]

meta initialize Check.register (α := MergeConsecutiveIntrosMatch)
