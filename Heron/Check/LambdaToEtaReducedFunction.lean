module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure LambdaToEtaReducedFunctionMatch where
  funStx : Syntax
  replaceStx : Syntax
  reduced : Term

private meta def etaReduced? (funStx : Syntax) : CommandElabM (Option Term) := do
  let `(fun $x:ident => $body) := funStx | return none
  let `($f $args*) := body | return none
  let some lastArgument := args.back? | return none
  let `($last:ident) := lastArgument | return none
  unless last.getId == x.getId do return none
  let #[_] ← boundVariableReferences x body | return none
  let reduced ← if args.size == 1 then pure f else `($f $(args.pop)*)
  unless ← elaboratesLike funStx reduced do return none
  return some reduced

private meta def detectEtaReducible (stx : Syntax) : CommandElabM (Array LambdaToEtaReducedFunctionMatch) := do
  let (funStx, replaceStx) : Syntax × Syntax := match stx with
    | `(($inner)) => (inner, stx)
    | _ => (stx, stx)
  let some reduced ← etaReduced? funStx | return #[]
  let reduced ← if ← needsParenthesesAt replaceStx reduced then `(($reduced)) else pure reduced
  return #[{ funStx, replaceStx, reduced }]

private meta instance : Check LambdaToEtaReducedFunctionMatch where
  name := `lambdaToEtaReducedFunction
  description := "Suggests `f a` instead of a lambda `fun x => f a x` that only passes its parameter on."
  kinds := #[``Term.paren, ``Term.fun]
  consumesSubtree := true
  severity := .information
  category := .simplification
  detect := detectEtaReducible
  message := fun m => m!"Use `{m.reduced}` instead of the lambda"
  emphasize := fun m => m.funStx
  sources := #[.hlint "Avoid lambda"]
  explanation := fun _ =>
    m!"A lambda whose body applies a function to the lambda's own parameter, as the last argument \
       and nowhere else, is that function: `fun x => f a x` is `f a`. The hint only appears where \
       the shorter form elaborates to the same function."
  replacements := some fun m => return #[{
    emphasizedSyntax := m.funStx
    oldSyntax := m.replaceStx
    newSyntax := m.reduced
    inlineViolationLabel := m!"eta reduction" }]

register_check LambdaToEtaReducedFunctionMatch
