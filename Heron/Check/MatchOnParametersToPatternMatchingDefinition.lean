module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure MatchedBinder where
  name : TSyntax `ident
  type : TSyntax `term

private structure MatchOnParametersToPatternMatchingDefinitionMatch where
  declaration : Syntax
  matchKw : Syntax
  modifiers : TSyntax ``Command.declModifiers
  declId : TSyntax ``Command.declId
  keptBinders : Array Syntax
  matched : Array MatchedBinder
  returnType : TSyntax `term
  alternatives : TSyntaxArray ``Term.matchAlt

private meta def simpleBinder? : Syntax → Option MatchedBinder
  | `(bracketedBinder| ($name:ident : $type)) => some { name, type }
  | _ => none

private meta def mentions (name : Name) (stx : Syntax) : Bool :=
  (stx.find? fun s => s.isIdent && (s.getId == name || s.getId.getRoot == name)).isSome

private meta def trailingBindersNamed (binders : Array Syntax) (discriminants : Array (TSyntax `term)) :
    Option (Array Syntax × Array MatchedBinder) := do
  let count := discriminants.size
  guard (count ≥ 1 && binders.size ≥ count)
  let kept := binders.extract 0 (binders.size - count)
  let trailing ← (binders.extract (binders.size - count)).mapM simpleBinder?
  guard (trailing.zip discriminants |>.all fun (binder, discr) =>
    match discr with
    | `($d:ident) => d.getId == binder.name.getId
    | _ => false)
  return (kept, trailing)

private meta def detectMatchOnParameters (cmd : Syntax) :
    Option MatchOnParametersToPatternMatchingDefinitionMatch := do
  let `($modifiers:declModifiers def $declId:declId $sig:optDeclSig :=
        match%$matchKw $[$discriminants:term],* with $alternatives:matchAlt*) := cmd | none
  let `(Command.optDeclSig| $binders* : $returnType) := sig | none
  let (keptBinders, matched) ← trailingBindersNamed binders discriminants
  let movedNames := matched.map (·.name.getId)
  guard (movedNames.all fun name =>
    !mentions name returnType && alternatives.all fun alt =>
      match alt with
      | `(Term.matchAltExpr| | $[$_,*]|* => $rhs) => !mentions name rhs
      | _ => false)
  return { declaration := cmd, matchKw, modifiers, declId, keptBinders, matched, returnType, alternatives }

private meta def patternMatchingDefinition (m : MatchOnParametersToPatternMatchingDefinitionMatch) :
    CommandElabM (TSyntax `command) := do
  let functionType ← m.matched.foldrM (init := m.returnType) fun binder acc => `($binder.type → $acc)
  let kept : TSyntaxArray ``Term.bracketedBinder := m.keptBinders.map (⟨·⟩)
  `($m.modifiers:declModifiers def $m.declId:declId $kept* : $functionType
      $m.alternatives:matchAlt*)

private meta instance : Check MatchOnParametersToPatternMatchingDefinitionMatch where
  name := `matchOnParametersToPatternMatchingDefinition
  description := "Suggests a pattern-matching definition instead of naming parameters only to `match` on them."
  kinds := #[]
  wholeCommand := true
  severity := .information
  category := .style
  detect := fun cmd => pure (detectMatchOnParameters cmd).toArray
  message := fun _ => m!"Match on the parameters directly with `def f : A → B | pattern => …`"
  emphasize := fun m => m.matchKw
  sources := #[.functionalProgrammingInLean "Pattern-matching definitions"
    "Getting-to-Know-Lean/Additional-Conveniences/#pattern-matching-definitions"]
  explanation := fun _ =>
    m!"When a parameter is named only to be matched on immediately, the cases can be written \
       directly after the signature: move the parameter's type to the right of the colon, so the \
       declared type becomes a function type, and replace `:= match … with` by the alternatives."
  replacements := some fun m => do
    return #[{
      emphasizedSyntax := m.matchKw
      oldSyntax := m.declaration
      newSyntax := ← patternMatchingDefinition m
      category := `command
      inlineViolationLabel := m!"match on parameters"
    }]

register_check MatchOnParametersToPatternMatchingDefinitionMatch
