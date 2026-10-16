module

public meta import Heron.Check
public meta import Heron.Monad

open Lean Elab Command Meta Parser Heron

private structure RedundantLetWildcardMatch where
  doLetStx : Syntax
  rhs : Syntax

/-- Match `let _ ← rhs`. -/
private meta def matchWildcardLetArrow? : Syntax → Option RedundantLetWildcardMatch
  | stx@`(doElem| let _ ← $rhs) => some { doLetStx := stx, rhs }
  | _ => none

private meta def returnsUnit? (action : Expr) : MetaM (Option Bool) := do
  let action ← instantiateMVars action
  if action.getAppFn.isMVar then return none
  let actionType ← whnfR (← instantiateMVars (← inferType action))
  if actionType.isSort then return none
  let some resultType := actionType.getAppArgs.back? | return some false
  return some (resultType.isConstOf ``Unit || resultType.isAppOf ``PUnit)

private meta def detectRedundantLetWildcards (doSeq : Syntax) :
    CommandElabM (Array RedundantLetWildcardMatch) :=
  (getDoElems doSeq).filterMapM fun elem => do
    let some m := matchWildcardLetArrow? elem | return none
    let verdicts := (← runMetaMForEachExactSyntax m.rhs returnsUnit?).filterMap id
    unless !verdicts.isEmpty && verdicts.all id do return none
    return some m

private meta instance : Check RedundantLetWildcardMatch where
  name := `redundantLetWildcard
  kinds := #[``Term.doSeqIndent, ``Term.doSeqBracketed]
  severity := .information
  category := .simplification
  detect := detectRedundantLetWildcards
  message := fun _ => m!"Redundant `let _ ←`"
  emphasize := fun m => m.doLetStx
  tags := #[.unnecessary]
  reference := none
  explanation := fun _ => m!"`action` already returns `Unit`, so `let _ ← action` can be simplified to just `action` in a do-block."
  replacements := fun m => return #[{
    emphasizedSyntax := m.doLetStx
    oldSyntax := m.doLetStx
    -- Drop the rhs's trailing trivia: a trailing comment lives there but sits *outside*
    -- `doLetStx`'s replaced range, so keeping it would duplicate the comment in the output.
    newSyntax := m.rhs.unsetTrailing
    inlineViolationLabel := m!"let _ ←"
  }]

meta initialize Check.register (α := RedundantLetWildcardMatch)
