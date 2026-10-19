module

public meta import Heron.Check
meta import Heron.Register

open Lean Elab Command Parser Heron

private structure SingleUseLambdaToCdotFunctionMatch where
  /-- The `fun x => body` node, used to anchor the diagnostic. -/
  funStx : Syntax
  /-- Node whose range is replaced: the enclosing `(…)` when the lambda is already
  parenthesised, otherwise `funStx` itself. Replacing the enclosing paren (rather than
  just the `fun`) keeps the output at a single set of parens — `(· + 1)`, not `((· + 1))`. -/
  replaceStx : Syntax
  cdotFunction : Term

private meta def cdotFunction (body : Term) (occurrence : Syntax) : CommandElabM Term := do
  `(($(body.replacingSourceNode occurrence (← `(·)))))

private meta def isBlockBody : Term → Bool
  | `(do $_) | `(let $_:letDecl; $_) | `($_:structInst) => true
  | _ => false

private meta def passesOccurrenceLast (body : Term) (occurrence : Syntax) : Bool :=
  match body with
  | `($_ $args*) => args.back?.any (·.raw == occurrence)
  | _ => false

/-- Match `fun x => body` where `x` is referenced exactly once, as a plain identifier, and
`(body)` with that reference replaced by `·` elaborates to the same function. -/
private meta def eligibleCdotFunction? (funStx : Syntax) : CommandElabM (Option Term) := do
  let `(fun $x:ident => $body) := funStx | return none
  if let `($_:ident) := body then return none
  if isBlockBody body then return none
  let #[occurrence] ← boundVariableReferences x body | return none
  let `($reference:ident) := occurrence | return none
  unless reference.getId == x.getId do return none
  if passesOccurrenceLast body occurrence then return none
  let candidate ← cdotFunction body occurrence
  unless ← elaboratesLike funStx candidate do return none
  return some candidate

private meta def detectSingleUseLambda (stx : Syntax) :
    CommandElabM (Array SingleUseLambdaToCdotFunctionMatch) := do
  let (funStx, replaceStx) : Syntax × Syntax := match stx with
    | `(($inner)) => (inner, stx)
    | _ => (stx, stx)
  let some cdotFunction ← eligibleCdotFunction? funStx | return #[]
  return #[{ funStx, replaceStx, cdotFunction }]

private meta instance : Check SingleUseLambdaToCdotFunctionMatch where
  name := `singleUseLambdaToCdotFunction
  description := "Suggests `·` instead of an explicit lambda whose parameter is used once."
  -- Also match `Term.paren` so a `(fun x => …)` is replaced as a unit (one set of parens).
  -- `consumesSubtree` then stops the inner `Term.fun` from re-matching and double-firing.
  kinds := #[``Term.paren, ``Term.fun]
  consumesSubtree := true
  severity := .information
  category := .simplification
  detect := detectSingleUseLambda
  message := fun _ => m!"Use `·` function shorthand instead of explicit lambda"
  emphasize := fun m => m.funStx
  sources := #[
    .functionalProgrammingInLean "Centered dot" "Getting-to-Know-Lean/Additional-Conveniences/#anonymous-functions",
    .mathlibStyleGuide "Anonymous functions" "anonymous-functions"]
  explanation := fun _ =>
    m!"Simple lambdas like `fun x => x + 1` can be written as `(· + 1)` using Lean's `·` function shorthand, which abstracts over the nearest enclosing parentheses."
  replacements := some fun m => return #[{
    emphasizedSyntax := m.funStx
    oldSyntax := m.replaceStx
    newSyntax := m.cdotFunction
    inlineViolationLabel := m!"fun → ·" }]

register_check SingleUseLambdaToCdotFunctionMatch
