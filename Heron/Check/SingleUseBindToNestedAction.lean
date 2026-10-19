module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

set_option linter.positionalSyntaxAccess false
set_option linter.sourcePositionInRule false
set_option linter.syntaxKindOrAtomInspection false
set_option linter.syntheticSyntaxConstruction false

open Lean Elab Command Parser Heron

private structure SingleUseBindToNestedActionMatch where
  bindStx : Syntax
  removedRange : Syntax
  use : Syntax
  action : TSyntax `term

private meta def singleIdentBind? : TSyntax `doElem → Option (TSyntax `ident × TSyntax `term)
  | `(doElem| let $x:ident ← $action:term) => some (x, action)
  | _ => none

private meta def opensNestedScope (kind : SyntaxNodeKind) : Bool :=
  [``Term.doSeqIndent, ``Term.doSeqBracketed, ``Term.fun, ``Term.matchAlts, ``Term.do].contains kind

private structure Occurrence where
  ident : Syntax
  underNestedScope : Bool

private meta partial def occurrencesOf (name : Name) (stx : Syntax) (underNestedScope := false) :
    Array Occurrence :=
  if stx.isIdent then
    if stx.getId == name || stx.getId.getRoot == name then #[{ ident := stx, underNestedScope }] else #[]
  else
    let nested := underNestedScope || opensNestedScope stx.getKind
    stx.getArgs.flatMap (occurrencesOf name · nested)

private meta def startsBefore (a b : Syntax) : Bool :=
  match a.getPos?, b.getPos? with
  | some p, some q => p < q
  | _, _ => false

private meta def isNestedAction : Syntax → Bool
  | `(← $_) => true
  | _ => false

private meta def nestedActionsIn (stx : Syntax) : Array Syntax :=
  (subtreeNodes stx).filter isNestedAction

private meta def spanUntil (first next : Syntax) : Option Syntax := do
  let start ← first.getPos?
  let stop ← next.getPos?
  return Syntax.ofRange ⟨start, stop⟩

private meta def pairToNestedAction? (bind next : TSyntax `doElem) (later : Array (TSyntax `doElem)) :
    Option SingleUseBindToNestedActionMatch := do
  let (x, action) ← singleIdentBind? bind
  let name := x.getId
  let #[use] := occurrencesOf name next | none
  guard (!use.underNestedScope && use.ident.getId == name)
  guard ((nestedActionsIn next).all (startsBefore use.ident ·))
  guard (later.all fun stmt => (occurrencesOf name stmt).isEmpty)
  let removedRange ← spanUntil bind next
  return { bindStx := bind, removedRange, use := use.ident, action }

private meta def detectSingleUseBinds (doSeq : Syntax) : Array SingleUseBindToNestedActionMatch :=
  let elems := getDoElems doSeq
  (Array.range elems.size).filterMap fun i => do
    let bind ← elems[i]?
    let next ← elems[i + 1]?
    pairToNestedAction? bind next (elems.extract (i + 2))

private meta instance : Check SingleUseBindToNestedActionMatch where
  name := `singleUseBindToNestedAction
  description := "Suggests a nested action `(← act)` instead of `let x ← act` when `x` is used once, in the next statement."
  kinds := #[``Term.doSeqIndent, ``Term.doSeqBracketed]
  severity := .information
  category := .style
  detect := fun stx => pure (detectSingleUseBinds stx)
  message := fun _ => m!"Use a nested action `(← …)` instead of binding a name that is used once"
  emphasize := fun m => m.bindStx
  sources := #[.functionalProgrammingInLean "Nested actions" "Monads/do--Notation-for-Monads/"]
  explanation := fun _ =>
    m!"Inside a `do` block, `(← act)` runs `act` just before the statement it appears in and \
       stands for its result, so a name bound with `let x ← act` and used once in the next \
       statement can be replaced by the nested action. Nested actions run left to right; the \
       rewrite is only offered when this keeps the order of effects."
  replacements := some fun m => do
    let nested ← `(term| (← $m.action))
    return #[
      { emphasizedSyntax := m.bindStx
        oldSyntax := m.removedRange
        newSyntax := Syntax.missing
        category := `doElem
        inlineViolationLabel := m!"bound once" },
      { emphasizedSyntax := m.use
        oldSyntax := m.use
        newSyntax := nested
        inlineViolationLabel := m!"nested action" }
    ]

register_check SingleUseBindToNestedActionMatch
