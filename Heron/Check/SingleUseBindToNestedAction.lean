module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure SingleUseBindToNestedActionMatch where
  bindStx : Syntax
  replacedRun : Syntax
  rewrittenNext : TSyntax `doElem

private meta def singleIdentBind? : TSyntax `doElem → Option (TSyntax `ident × TSyntax `term)
  | `(doElem| let $x:ident ← $action:term) => some (x, action)
  | _ => none

private meta def isSingleStatement : TSyntax `doElem → Bool
  | `(doElem| let $_:ident := $_) | `(doElem| let $_:ident ← $_) | `(doElem| return $_)
  | `(doElem| $_:term) => true
  | _ => false

private meta def nestedAction (action : Term) : CommandElabM Term := do
  `(term| (← $action))

private meta def singleUseInNext? (x : Ident) (next : TSyntax `doElem) (rest : Array (TSyntax `doElem)) :
    CommandElabM (Option Syntax) := do
  let #[use] ← boundVariableReferences x next | return none
  for later in rest do
    unless (← boundVariableReferences x later).isEmpty do return none
  let `($reference:ident) := use | return none
  unless reference.getId == x.getId do return none
  return some use

private meta def pairToNestedAction? (doTerm : Syntax) (elems : Array (TSyntax `doElem)) (i : Nat) :
    CommandElabM (Option SingleUseBindToNestedActionMatch) := do
  let some bind := elems[i]? | return none
  let some next := elems[i + 1]? | return none
  unless isSingleStatement next do return none
  let some (x, action) := singleIdentBind? bind | return none
  let some use ← singleUseInNext? x next (elems.extract (i + 2)) | return none
  let rewrittenNext := next.replacingSourceNode use (← nestedAction action)
  let candidateElems := elems.extract 0 i ++ #[rewrittenNext] ++ elems.extract (i + 2)
  unless ← elaboratesLike doTerm (← doBlockOf candidateElems) do return none
  return some { bindStx := bind, replacedRun := mkNullNode #[bind, next], rewrittenNext }

private meta def detectSingleUseBinds (doTerm : Syntax) :
    CommandElabM (Array SingleUseBindToNestedActionMatch) := do
  let `(do $seq) := doTerm | return #[]
  let elems := getDoElems seq
  (Array.range elems.size).filterMapM (pairToNestedAction? doTerm elems)

private meta instance : Check SingleUseBindToNestedActionMatch where
  name := `singleUseBindToNestedAction
  description := "Suggests a nested action `(← act)` instead of `let x ← act` when `x` is used once, in the next statement."
  kinds := #[``Term.do]
  severity := .information
  category := .style
  detect := detectSingleUseBinds
  message := fun _ => m!"Use a nested action `(← …)` instead of binding a name that is used once"
  emphasize := fun m => m.bindStx
  sources := #[.functionalProgrammingInLean "Nested actions" "Monads/do--Notation-for-Monads/"]
  explanation := fun _ =>
    m!"Inside a `do` block, `(← act)` runs `act` just before the statement it appears in and \
       stands for its result, so a name bound with `let x ← act` and used once in the next \
       statement can be replaced by the nested action. Nested actions run left to right; the \
       rewrite is only offered when this keeps the order of effects."
  replacements := some fun m => return #[{
    emphasizedSyntax := m.bindStx
    oldSyntax := m.replacedRun
    newSyntax := m.rewrittenNext
    prettyPrint := PrettyPrinter.ppCategory `doElem
    inlineViolationLabel := m!"bound once" }]

register_check SingleUseBindToNestedActionMatch
