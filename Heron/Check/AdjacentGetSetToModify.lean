module

public meta import Heron.Check
public meta import Heron.Monad

open Lean Elab Command Parser Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private meta def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure AdjacentGetSetToModifyMatch where
  getStx : Syntax
  setStx : Syntax
  fullRange : Syntax
  varName : Syntax
  structInst : Syntax

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

/-- Check if a variable name appears anywhere in a syntax tree,
either as an exact ident match or as the leading component of a dotted name. -/
private meta partial def containsName (varName : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then
    let n := stx.getId
    n == varName || n.getRoot == varName
  else
    stx.getArgs.any (containsName varName)

/-- For a get-binding at index `i`, match a `set` directly after it whose state
binding is not used by any later element. -/
private meta def findSetForGet (elems : Array (TSyntax `doElem)) (i : Nat)
    (getElem : TSyntax `doElem) (varNameStx : TSyntax `ident)
    : Option AdjacentGetSetToModifyMatch := do
  let varName := varNameStx.getId
  let (setElem, structInst) ← isSetWithStructUpdate? (← elems[i + 1]?) varName
  guard !((elems.extract (i + 2)).any fun later => containsName varName later)
  return {
    getStx := getElem
    setStx := setElem
    fullRange := mkSpan getElem setElem |>.getD getElem
    varName := varNameStx
    structInst
  }

private meta def detectGetSetToModify (doSeq : Syntax) : Array AdjacentGetSetToModifyMatch :=
  let elems := getDoElems doSeq
  (Array.range elems.size).filterMap fun i =>
    match isGetBinding? elems[i]! with
    | some (getElem, varName) => findSetForGet elems i getElem varName
    | none => none

private meta instance : Check AdjacentGetSetToModifyMatch where
  name := `adjacentGetSetToModify
  kinds := #[``Term.doSeqIndent, ``Term.doSeqBracketed]
  severity := .warning
  category := .simplification
  detect := fun stx => pure (detectGetSetToModify stx)
  message := fun _ => m!"Use `modify` instead of `get`/`set`"
  emphasize := fun m => m.fullRange
  reference := some { topic := "State", url := "https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/A-Monad-Construction-Kit/#state-monad" }
  explanation := fun _ =>
    m!"`let s ← get; set \{s with ...}` can be written `modify fun s => \{s with ...}`. Besides being \
       shorter, `modify` rules out writing back a stale copy of the state (`set s` where `set s'` \
       was meant), and it keeps a single reference to the state, which the compiler needs to \
       update it in place instead of copying it."
  replacements := fun m => do
    let varId : TSyntax `ident := ⟨m.varName⟩
    let structInst : TSyntax `term := ⟨m.structInst⟩
    let modifyId := mkIdent `modify
    let repl ← `(doElem| $modifyId:ident fun $varId => $structInst)
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

meta initialize Check.register (α := AdjacentGetSetToModifyMatch)
