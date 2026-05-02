module

public meta import Heron.Check

open Lean Elab Command Parser Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private meta def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure GetSetToModifyMatch where
  getStx : Syntax
  setStx : Syntax
  fullRange : Syntax
  varName : Syntax
  structInst : Syntax

/-- Check if a do-element is `let <name> ← get`. -/
private meta def isGetBinding? : Syntax → Option (Syntax × Syntax)
  | elem@`(doElem| let $x ← get) => some (elem, x)
  | _ => none

/-- Check if a do-element is `set { <name> with ... }`. -/
private meta def isSetWithStructUpdate? (elem : Syntax) (varName : Name) : Option (Syntax × Syntax) :=
  match elem with
  | `(doElem| set { $src with $fields,* }) =>
    if src.raw.getId == varName then
      -- Extract the structInst node from inside the app
      let arg := elem[0]![1]![0]!
      some (elem, arg)
    else none
  | _ => none

/-- Check if a variable name appears anywhere in a syntax tree,
either as an exact ident match or as the leading component of a dotted name. -/
private meta partial def containsName (varName : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then
    let n := stx.getId
    n == varName || n.getRoot == varName
  else
    stx.getArgs.any (containsName varName)

/-- For a given get-binding at index `i`, find the matching set call. -/
private meta def findSetForGet (elems : Array Syntax) (i : Nat) (getElem : Syntax) (varNameStx : Syntax)
    : Option GetSetToModifyMatch :=
  let varName := varNameStx.getId
  let rec go (j : Nat) : Option GetSetToModifyMatch :=
    if h : j < elems.size then
      match isSetWithStructUpdate? elems[j] varName with
      | some (setElem, structInst) =>
        -- Check that varName is not used between get and set
        let usedBetween := (List.range (j - i - 1)).any fun k =>
          containsName varName elems[i + 1 + k]!
        if !usedBetween then
          some {
            getStx := getElem
            setStx := setElem
            fullRange := mkSpan getElem setElem |>.getD getElem
            varName := varNameStx
            structInst
          }
        else none
      | none =>
        if containsName varName elems[j] then none
        else go (j + 1)
    else none
  go (i + 1)

private meta def detectGetSetToModify (doSeq : Syntax) : Array GetSetToModifyMatch :=
  let elems := getDoElems doSeq
  (Array.range elems.size).filterMap fun i =>
    match isGetBinding? elems[i]! with
    | some (getElem, varName) => findSetForGet elems i getElem varName
    | none => none

private meta instance : Check GetSetToModifyMatch where
  name := `getSetToModify
  kinds := #[``Term.doSeqIndent, ``Term.doSeqBracketed]
  severity := .warning
  category := .simplification
  detect := fun stx => pure (detectGetSetToModify stx)
  message := fun _ => m!"Use `modify` instead of `get`/`set`"
  emphasize := fun m => m.fullRange
  reference := some { topic := "modify", url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/transformers.html" }
  explanation := fun _ => m!"`let s ← get; set \{s with ...}` can be simplified to `modify fun s => \{s with ...}`."
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

meta initialize Check.register (α := GetSetToModifyMatch)
