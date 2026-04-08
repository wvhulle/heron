import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure GetSetMatch where
  getStx : Syntax
  setStx : Syntax
  fullRange : Syntax
  varName : Syntax
  structInst : Syntax

/-- Check if a do-element is `let <name> ← get`. -/
private def isGetBinding? : Syntax → Option (Syntax × Syntax)
  | elem@`(doElem| let $x ← get) => some (elem, x)
  | _ => none

/-- Check if a do-element is `set { <name> with ... }`. -/
private def isSetWithStructUpdate? (elem : Syntax) (varName : Name) : Option (Syntax × Syntax) :=
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
private partial def containsName (varName : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then
    let n := stx.getId
    n == varName || n.getRoot == varName
  else
    stx.getArgs.any (containsName varName)

/-- For a given get-binding at index `i`, find the matching set call. -/
private def findSetForGet (elems : Array Syntax) (i : Nat) (getElem : Syntax) (varNameStx : Syntax)
    : Option GetSetMatch :=
  let varName := varNameStx.getId
  let rec go (j : Nat) : Option GetSetMatch :=
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

/-- Find `let s ← get; set \{s with ...}` patterns. -/
private def findGetSet (stx : Syntax) : Array GetSetMatch :=
  let doSeqs := Syntax.collectAll (fun s =>
    if s.isOfKind ``Term.doSeqIndent || s.isOfKind ``Term.doSeqBracketed then #[s]
    else #[]) stx
  doSeqs.flatMap fun doSeq =>
    let elems := getDoElems doSeq
    (Array.range elems.size).filterMap fun i =>
      match isGetBinding? elems[i]! with
      | some (getElem, varName) => findSetForGet elems i getElem varName
      | none => none

@[check_rule] instance : Check GetSetMatch where
  ruleName := `getSet
  severity := .warning
  category := .simplification
  pureDetect := findGetSet
  message := fun _ => m!"Use `modify` instead of `get`/`set`"
  node := fun m => m.fullRange
  reference := some { topic := "modify", url := "https://lean-lang.org/functional_programming_in_lean/monad-transformers/do.html" }
  explanation := fun _ => m!"`let s ← get; set \{s with ...}` can be simplified to `modify fun s => \{s with ...}`."
  replacements := fun m => do
    let varId : TSyntax `ident := ⟨m.varName⟩
    let structInst : TSyntax `term := ⟨m.structInst⟩
    let modifyId := mkIdent `modify
    let repl ← `(doElem| $modifyId:ident fun $varId => $structInst)
    return #[
      { sourceNode := m.getStx
        targetNode := m.getStx
        insertText := repl
        category := `doElem
        sourceLabel := m!"get/set → modify" },
      { sourceNode := m.setStx
        targetNode := m.setStx
        insertText := Syntax.missing
        category := `doElem
        sourceLabel := m!"remove set" }
    ]

namespace Tests

private structure MyState where
  count : Nat
  name : String

-- Basic get/set to modify
#assertCheck getSet in
def inc : StateM MyState Unit := do
  let s ← get
  set { s with count := s.count + 1 }
becomes `(command|
def inc : StateM MyState Unit := do
  modify fun s => { s with count := s.count + 1 })

-- Ignore: variable used between get and set
#assertIgnore getSet in
def f : StateM MyState Unit := do
  let st ← get
  IO.println s!"{st.count}"
  set { st with count := 0 }

-- Ignore: no set call
#assertIgnore getSet in
def g : StateM MyState Nat := do
  let s ← get
  pure s.count

end Tests
