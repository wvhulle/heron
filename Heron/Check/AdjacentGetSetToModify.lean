module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure AdjacentGetSetToModifyMatch where
  getStx : Syntax
  setStx : Syntax
  fullRange : Syntax
  varName : Ident
  structInst : TSyntax ``Lean.Parser.Term.structInst

/-- Check if a do-element is `let <name> ← get`. -/
private meta def isGetBinding? : TSyntax `doElem → Option (TSyntax `doElem × TSyntax `ident)
  | elem@`(doElem| let $x ← get) => some (elem, x)
  | _ => none

/-- Check if a do-element is `set { <name> with ... }`. -/
private meta def isSetWithStructUpdate? (elem : TSyntax `doElem) (varName : Name) :
    Option (TSyntax `doElem × TSyntax `Lean.Parser.Term.structInst) :=
  match elem with
  | `(doElem| set $upd:structInst) =>
    match upd with
    | `({ $src:ident with $_,* }) =>
      if src.getId == varName then some (elem, upd) else none
    | _ => none
  | _ => none

/-- For a get-binding at index `i`, match a `set` directly after it whose state
binding is not used by any later element. -/
private meta def findSetForGet (elems : Array (TSyntax `doElem)) (i : Nat)
    (getElem : TSyntax `doElem) (varName : Ident) : CommandElabM (Option AdjacentGetSetToModifyMatch) := do
  let some next := elems[i + 1]? | return none
  let some (setElem, structInst) := isSetWithStructUpdate? next varName.getId | return none
  for later in elems.extract (i + 2) do
    unless (← boundVariableReferences varName later).isEmpty do return none
  return some {
    getStx := getElem
    setStx := setElem
    fullRange := mkNullNode #[getElem, setElem]
    varName
    structInst
  }

private meta def detectGetSetToModify (doSeq : Syntax) : CommandElabM (Array AdjacentGetSetToModifyMatch) := do
  let elems := getDoElems doSeq
  (Array.range elems.size).filterMapM fun i => do
    let some elem := elems[i]? | return none
    let some (getElem, varName) := isGetBinding? elem | return none
    findSetForGet elems i getElem varName

set_option hygiene false in
private meta def modifyCall (m : AdjacentGetSetToModifyMatch) : CommandElabM (TSyntax `doElem) :=
  `(doElem| modify fun $m.varName => $m.structInst:structInst)

private meta instance : Check AdjacentGetSetToModifyMatch where
  name := `adjacentGetSetToModify
  description := "Suggests `modify` instead of `get` directly followed by `set`."
  kinds := #[``Term.doSeqIndent, ``Term.doSeqBracketed]
  severity := .warning
  category := .simplification
  detect := detectGetSetToModify
  message := fun _ => m!"Use `modify` instead of `get`/`set`"
  emphasize := fun m => m.fullRange
  sources := #[.functionalProgrammingInLean "State" "Monad-Transformers/A-Monad-Construction-Kit/#state-monad"]
  explanation := fun _ =>
    m!"`let s ← get; set \{s with ...}` can be written `modify fun s => \{s with ...}`. Besides being \
       shorter, `modify` rules out writing back a stale copy of the state (`set s` where `set s'` \
       was meant), and it keeps a single reference to the state, which the compiler needs to \
       update it in place instead of copying it."
  replacements := some fun m => do
    let repl ← modifyCall m
    return #[
      { emphasizedSyntax := m.getStx
        oldSyntax := m.getStx
        newSyntax := repl
        category := `doElem
        inlineViolationLabel := m!"get/set → modify" },
      { emphasizedSyntax := m.setStx
        oldSyntax := m.setStx
        newSyntax := Syntax.missing
        category := `doElem
        inlineViolationLabel := m!"remove set" }
    ]
  labels := fun m => return #[
    { span := m.varName
      text := m!"state binding `{m.varName}` becomes the parameter of `modify`" },
    { span := m.structInst
      text := m!"structure update reused as the body of `modify`" }
  ]

register_check AdjacentGetSetToModifyMatch
