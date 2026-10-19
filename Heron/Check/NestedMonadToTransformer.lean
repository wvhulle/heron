module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Meta Parser Heron

private structure NestedMonadToTransformerMatch where
  stx : Syntax
  nestedMonad : Name
  transformerType : Term

private meta def appliedOuterMonad (outerFn : Ident) (outerLeading : TSyntaxArray `term) : CommandElabM Term :=
  if outerLeading.isEmpty then pure outerFn else `(($outerFn $outerLeading*))

set_option hygiene false in
private meta def nestedMonadAndTransformer? : Syntax → CommandElabM (Option (Name × Term))
  | `($outerFn:ident $outerLeading* (Option $α $αs*)) => do
    let outer ← appliedOuterMonad outerFn outerLeading
    return some (``Option, ← `(OptionT $(#[outer, α] ++ αs)*))
  | `($outerFn:ident $outerLeading* (Except $ε $α $αs*)) => do
    let outer ← appliedOuterMonad outerFn outerLeading
    return some (``Except, ← `(ExceptT $(#[ε, outer, α] ++ αs)*))
  | _ => return none

private meta def wrapsInAnotherMonad (nestedMonad : Name) (e : Expr) : MetaM Bool := do
  if e.getAppFn.isConstOf nestedMonad then return false
  outerHasMonadInstance e

private meta def detectInSignature (node : Syntax) : CommandElabM (Array NestedMonadToTransformerMatch) := do
  let some (nestedMonad, transformerType) ← nestedMonadAndTransformer? node | return #[]
  let some true ← runMetaMForSyntax node (wrapsInAnotherMonad nestedMonad) | return #[]
  unless ← rewriteElaborates node transformerType do return #[]
  return #[{ stx := node, nestedMonad, transformerType }]

private meta instance : Check NestedMonadToTransformerMatch where
  name := `nestedMonadToTransformer
  description := "Suggests `OptionT` or `ExceptT` instead of nesting `Option` or `Except` inside another monad in a signature whose definition already elaborates with the transformer."
  kinds := #[``Term.app]
  within := #[``Command.declSig, ``Command.optDeclSig]
  severity := .information
  category := .style
  detect := detectInSignature
  message := fun m => m!"Consider `{m.transformerType}` instead of nesting `{m.nestedMonad}` in another monad"
  emphasize := fun m => m.stx
  sources := #[
    .functionalProgrammingInLean "OptionT" "Monad-Transformers/A-Monad-Construction-Kit/#OptionT",
    .functionalProgrammingInLean "ExceptT" "Monad-Transformers/A-Monad-Construction-Kit/#exceptions"]
  explanation := fun _ =>
    m!"`OptionT m α` is defined as `m (Option α)` and `ExceptT ε m α` as `m (Except ε α)`, so \
       this signature already is the transformer type, and the definition elaborates unchanged \
       with it. Writing the transformer lets `do`-notation handle the failure case: `failure` or \
       `throw` short-circuits and a `let x ← act` binds the value. Changing a signature can break \
       callers in other declarations, which may need `.run`, so no automatic fix is offered."

register_check NestedMonadToTransformerMatch
