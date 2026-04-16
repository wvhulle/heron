module

public meta import Heron.Check

open Lean Elab Command Parser Heron

/-- Get the variable name from a doLet's letIdDecl. -/
private meta def getDoLetVarName? (doLet : Syntax) : Option Name :=
  if doLet.getKind == ``Term.doLet then
    let letDecl := doLet[2]!  -- doLet[0]="let", [1]=optional mut, [2]=letDecl
    let inner := letDecl[0]!  -- letIdDecl (or letPatDecl)
    if inner.getKind == ``Term.letIdDecl then
      let letId := inner[0]!
      if letId.getKind == ``Term.letId then
        let ident := letId[0]!
        if ident.isIdent then some ident.getId else none
      else none
    else none
  else none

/-- Check if a doLet has the `mut` keyword. -/
private meta def hasMut (doLet : Syntax) : Bool :=
  doLet.getKind == ``Term.doLet && !doLet[1]!.getArgs.isEmpty

/-- Get the variable name from a doReassign's letIdDecl. -/
private meta def getReassignVarName? (elem : Syntax) : Option Name :=
  if elem.getKind == ``Term.doReassign then
    let letIdDecl := elem[0]!
    if letIdDecl.getKind == ``Term.letIdDecl then
      let letId := letIdDecl[0]!
      if letId.getKind == ``Term.letId then
        let ident := letId[0]!
        if ident.isIdent then some ident.getId else none
      else none
    else none
  else none

/-- Collect all reassigned variable names from a list of doElems (recursively into nested blocks). -/
private meta partial def collectReassignedVars (elems : Array Syntax) : Std.HashSet Name :=
  elems.foldl (init := {}) fun acc elem =>
    let k := elem.getKind
    if k == ``Term.doReassign then
      match getReassignVarName? elem with
      | some name => acc.insert name
      | none => acc
    else
      -- Also search children for reassignments in nested blocks
      elem.getArgs.foldl (fun acc child =>
        collectReassignedVars (getDoElems child) |>.fold (init := acc) fun acc n => acc.insert n
      ) acc

private structure UnnecessaryMutMatch where
  doLetStx : Syntax
  mutKeyword : Syntax
  ident : TSyntax `ident
  valStx : TSyntax `term

/-- Find `let mut x := e` where x is never reassigned in the subsequent do-elements. -/
private meta def findUnnecessaryMuts (stx : Syntax) : Array UnnecessaryMutMatch :=
  -- Find all do blocks first
  let doSeqs := Syntax.collectAll (fun s =>
    if s.getKind == ``Term.doSeqIndent || s.getKind == ``Term.doSeqBracketed then #[s]
    else #[]) stx  -- collectAll concatenates results; #[] for non-matches is correct
  doSeqs.flatMap fun doSeq =>
    let elems := getDoElems doSeq
    let reassigned := collectReassignedVars elems
    elems.filterMap fun elem =>
      if hasMut elem then
        match getDoLetVarName? elem with
        | some name =>
          if !reassigned.contains name then
            let mutKw := elem[1]![0]!
            -- Extract ident and value from letIdDecl
            let letDecl := elem[2]![0]!  -- letIdDecl
            let ident : TSyntax `ident := ⟨letDecl[0]![0]!⟩
            let valStx : TSyntax `term := ⟨letDecl[4]!⟩
            some { doLetStx := elem, mutKeyword := mutKw, ident, valStx }
          else none
        | none => none
      else none

@[check_rule] private meta instance : Check UnnecessaryMutMatch where
  name := `unnecessaryMut
  severity := .warning
  category := .simplification
  find := findUnnecessaryMuts
  message := fun _ => m!"Remove unnecessary `mut`"
  emphasize := fun m => m.mutKeyword
  reference := some { topic := "`let mut`", url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/do.html#mutable-variables" }
  tags := #[.unnecessary]
  explanation := fun _ => m!"This variable is declared `mut` but never reassigned. Use `let` instead of `let mut` to signal immutability."
  replacements := fun m => do
    let repl ← `(doElem| let $m.ident := $m.valStx)
    return #[{
      emphasizedSyntax := m.doLetStx
      oldSyntax := m.doLetStx
      newSyntax := repl
      category := `doElem
      inlineViolationLabel := m!"unused mut"
    }]
