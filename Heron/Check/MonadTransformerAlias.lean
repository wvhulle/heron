import Heron.Check
import Heron.Assert

open Lean Elab Command Meta Parser Heron

private structure MonadTransformerAliasMatch where
  stx : Syntax
  transformerName : String
  outerFn : Syntax
  outerArgs : Array Syntax
  innerFn : Syntax
  innerArgs : Array Syntax

/-- Map inner type constructor to its transformer name. -/
private def transformerFor? : String → Option String
  | "Option" => some "OptionT"
  | "Except" => some "ExceptT"
  | _ => none

/-- A syntactic candidate before Monad verification. -/
private structure Candidate where
  fullStx : Syntax
  transformerName : String
  outerFn : Syntax
  outerArgs : Array Syntax
  innerFn : Syntax
  innerArgs : Array Syntax

/-- Build the replacement text for a transformer alias. -/
private def buildReplacement (outerFn : String) (outerArgs : Array Syntax)
    (innerFn : String) (innerArgs : Array Syntax) (tName : String) : String :=
  let outerLeading := outerArgs.pop.map reprintTrimmed
  let outerMonadText :=
    if outerLeading.isEmpty then outerFn
    else s!"({outerFn} {" ".intercalate outerLeading.toList})"
  let innerArgTexts := innerArgs.map reprintTrimmed
  if innerFn == "Except" && innerArgTexts.size >= 2 then
    -- ExceptT ε m α₁ … αₙ
    let parts := #[tName, innerArgTexts[0]!, outerMonadText]
      ++ innerArgTexts.extract 1 innerArgTexts.size
    " ".intercalate parts.toList
  else
    -- OptionT m α₁ … αₙ
    " ".intercalate (#[tName, outerMonadText] ++ innerArgTexts).toList

/-- Detect a candidate at a single node: `f ... (Option α)` or `f ... (Except ε α)`.
Excludes cases where outer and inner constructor match (handled by NestedMonadJoin). -/
private def detectCandidate? : Syntax → Option Candidate
  | stx@`($outerFn $outerArgs*) => do
    guard outerFn.raw.isIdent
    guard (outerArgs.size > 0)
    let inner ← match outerArgs[outerArgs.size - 1]! with
      | `(($inner)) => some inner
      | _ => none
    let (innerFn, innerArgs) ← match inner with
      | `($fn $args*) => some (fn, args)
      | _ => none
    guard innerFn.raw.isIdent
    let outerName := reprintTrimmed outerFn
    let innerName := reprintTrimmed innerFn
    guard (outerName != innerName)
    let tName ← transformerFor? innerName
    let outerRawArgs := stx[1]!.getArgs
    let innerRawArgs := inner.raw[1]!.getArgs
    guard (innerRawArgs.size > 0)
    return {
      fullStx := stx
      transformerName := tName
      outerFn := outerFn
      outerArgs := outerRawArgs
      innerFn := innerFn
      innerArgs := innerRawArgs
    }
  | _ => none

/-- Find syntactic candidates across the whole syntax tree. -/
private def findCandidates : Syntax → Array Candidate :=
  Syntax.collectAll fun stx =>
    match detectCandidate? stx with
    | some c => #[c]
    | none => #[]

/-- Check if the outer part of an expression (everything except the last arg) has a Monad instance. -/
private def outerHasMonadInstance (e : Expr) : MetaM Bool := do
  let args := e.getAppArgs
  if args.size == 0 then 
    return false
  let outerMonad := mkAppN e.getAppFn args.pop
  try
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let monadType := mkAppN (mkConst ``Monad [u, v]) #[outerMonad]
    return (← synthInstance? monadType).isSome
  catch _ =>
    return false

private def detectMonadTransformerAliases (stx : Syntax) : CommandElabM (Array MonadTransformerAliasMatch) := do
  let candidates := findCandidates stx
  if candidates.isEmpty then 
    return #[]
  let trees ← collectInfoTrees stx
  let infos := trees.flatMap collectTermInfos
  let deduped := deduplicateTermInfos infos
  let posMap :=
    deduped.foldl (init := ({ } : Std.HashMap Nat (ContextInfo × TermInfo))) fun map (ci, ti) =>
      match ti.stx.getPos? true with
      | some pos => map.insert pos.byteIdx (ci, ti)
      | none => map
  let mut results : Array MonadTransformerAliasMatch := #[]
  for cand in candidates do
    match cand.fullStx.getPos? true with
    | some pos =>
      match posMap[pos.byteIdx]? with
      | some (ci, ti) =>
        let hasMonad ← runInfoMetaM ci ti.lctx (outerHasMonadInstance ti.expr)
        if hasMonad then 
          results :=
            results.push
              { stx := cand.fullStx
                transformerName := cand.transformerName
                outerFn := cand.outerFn
                outerArgs := cand.outerArgs
                innerFn := cand.innerFn
                innerArgs := cand.innerArgs }
      | none =>
        pure ()
    | none =>
      pure ()
  return results

@[check_rule]
instance : Check MonadTransformerAliasMatch
    where
  ruleName := `monadTransformerAlias
  severity := .information
  category := .style
  detect := detectMonadTransformerAliases
  message := fun m => m! "Consider using `{m.transformerName}` instead of nesting"
  node := fun m => m.stx
  tags := #[]
  reference :=
    some
      { topic := "Monad transformers"
        url := "https://lean-lang.org/functional_programming_in_lean/monads/transformers.html" }
  explanation := fun m => m! "This nested monad type is definitionally equal to its `{m.transformerName}` form. \
       Using the transformer alias enables do-notation with automatic effect handling."
  replacements := fun m => do
    let tName := mkIdent (Name.mkSimple m.transformerName)
    -- Build outer monad: if no leading args, just outerFn; else (outerFn args...)
    let outerLeading := m.outerArgs.pop.filter (!·.isAtom)
    let outerMonad : TSyntax `term ←
      if outerLeading.isEmpty then pure ⟨m.outerFn⟩
      else
        let outerFn : TSyntax `term := ⟨m.outerFn⟩
        let leading : TSyntaxArray `term := outerLeading.map (⟨·⟩)
        `(($outerFn $leading*))
    -- Build replacement: tName [innerLeadingArgs...] outerMonad [innerTrailingArgs...]
    let innerArgsSyn := m.innerArgs.filter (!·.isAtom)
    let allArgs : Array (TSyntax `term) :=
      if reprintTrimmed m.innerFn == "Except" && innerArgsSyn.size >= 2 then
        #[⟨innerArgsSyn[0]!⟩, outerMonad] ++ (innerArgsSyn.extract 1 innerArgsSyn.size).map (⟨·⟩)
      else
        #[outerMonad] ++ innerArgsSyn.map (⟨·⟩)
    let allArgs : TSyntaxArray `term := allArgs
    let repl ← `($tName $allArgs*)
    return #[{ sourceNode := m.stx
               targetNode := m.stx
               insertText := repl
               sourceLabel := m!"transformer alias" }]

namespace Tests

-- IO wrapping Option with polymorphic return type and multiple parameters
#assertCheck monadTransformerAlias in
def tryLookup {α : Type} (table : List (String × α)) (key : String) : IO (Option α) := sorry
becomes `(def tryLookup {α : Type} (table : List (String × α)) (key : String) : OptionT IO α := sorry)

-- IO wrapping Except with compound error type
#assertCheck monadTransformerAlias in
def parseConfig (path : String) (strict : Bool) : IO (Except (List String) Nat) := sorry
becomes `(def parseConfig (path : String) (strict : Bool) : ExceptT (List String) IO Nat := sorry)

-- Outer monad with args (Except as outer wrapping Option) — outer needs parens
#assertCheck monadTransformerAlias in
def validate (input : String) : Except String (Option Nat) := sorry
becomes `(def validate (input : String) : OptionT (Except String) Nat := sorry)

-- No outer monad wrapping — plain Option
#assertIgnore monadTransformerAlias in
  def h : Option Nat :=
    sorry

-- No outer monad wrapping — plain Except
#assertIgnore monadTransformerAlias in
  def k : Except String Nat :=
    sorry

-- Same-constructor nesting belongs to NestedMonadJoin, not this check
#assertIgnore monadTransformerAlias in
  def l : Option (Option Nat) :=
    sorry

end Tests
