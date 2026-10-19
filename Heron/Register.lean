module

public meta import Lean.Elab.Command
public meta import Heron.Check
public meta import Heron.Refactor
meta import Lean.Elab.Eval

public section

namespace Heron.Register

open Lean Elab Command Term Parser

meta def selfLints : Array Name := #[
  `positionalSyntaxAccess, `syntaxKindOrAtomInspection, `syntheticSyntaxConstruction,
  `sourcePositionInRule, `sourceTextInRule, `syntaxKindComparisonToQuotationPattern,
  `tsyntaxRawToTypedAccess]

meta initialize selfLints.forM registerLinterOption

private meta unsafe def evalRuleKindsUnsafe (rule : Ident) : TermElabM (Array Name) := do
  evalTerm (Array Name) (mkApp (mkConst ``Array [Level.zero]) (mkConst ``Name))
    (← `(Heron.Rule.kinds (α := $rule)))

@[implemented_by evalRuleKindsUnsafe]
private meta opaque evalRuleKinds (rule : Ident) : TermElabM (Array Name)

private meta unsafe def evalWholeCommandUnsafe (rule : Ident) : TermElabM Bool := do
  evalTerm Bool (mkConst ``Bool) (← `(Heron.Rule.wholeCommand (α := $rule)))

@[implemented_by evalWholeCommandUnsafe]
private meta opaque evalWholeCommand (rule : Ident) : TermElabM Bool

private meta unsafe def evalOffersFixUnsafe (rule : Ident) : TermElabM Bool := do
  evalTerm Bool (mkConst ``Bool) (← `(Heron.Rule.offersFix (α := $rule)))

@[implemented_by evalOffersFixUnsafe]
private meta opaque evalOffersFix (rule : Ident) : TermElabM Bool

private meta def checkRefactorHasReplacements (rule : Ident) : CommandElabM Unit := do
  unless ← liftTermElabM (evalOffersFix rule) do
    throwErrorAt rule m!"refactor `{rule}` has no `replacements`; a refactor must rewrite code"

private meta def checkKinds (rule : Ident) : CommandElabM Unit := do
  let kinds ← liftTermElabM (evalRuleKinds rule)
  let wholeCommand ← liftTermElabM (evalWholeCommand rule)
  if kinds.isEmpty && !wholeCommand then
    throwErrorAt rule m!"rule `{rule}` has `kinds := #[]`: declare the node kinds it fires on, \
      or set `wholeCommand := true` if it must analyse each whole command"
  if !kinds.isEmpty && wholeCommand then
    throwErrorAt rule m!"rule `{rule}` sets `wholeCommand := true` but also lists `kinds`"
  let env ← getEnv
  for kind in kinds do
    unless isValidSyntaxNodeKind env kind do
      throwErrorAt rule m!"rule `{rule}` lists `{kind}` in `kinds`, which is not a syntax node kind"

private meta def checkTestFiles (rule : Ident) : CommandElabM Unit := do
  let ruleFile : System.FilePath := ← getFileName
  let testDir := ruleFile.withExtension ""
  for test in ["Detects.lean", "Ignores.lean"] do
    unless ← (testDir / test).pathExists do
      throwErrorAt rule m!"rule `{rule}` has no `{testDir / test}`; every rule needs \
        `Detects.lean` and `Ignores.lean` next to its file"

private meta def runStructuralChecks (rule : Ident) : CommandElabM Unit := do
  checkKinds rule
  checkTestFiles rule

syntax (name := registerCheckCmd) "register_check " ident : command

syntax (name := registerRefactorCmd) "register_refactor " ident : command

@[command_elab registerCheckCmd] meta def elabRegisterCheck : CommandElab
  | `(register_check $rule:ident) => do
    elabCommand (← `(meta initialize Heron.Check.register (α := $rule)))
    runStructuralChecks rule
  | _ => throwUnsupportedSyntax

@[command_elab registerRefactorCmd] meta def elabRegisterRefactor : CommandElab
  | `(register_refactor $rule:ident) => do
    elabCommand (← `(meta initialize Heron.Refactor.register (α := $rule)))
    runStructuralChecks rule
    checkRefactorHasReplacements rule
  | _ => throwUnsupportedSyntax

end Heron.Register
