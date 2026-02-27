import Heron.Diagnostic
import Heron.Assert

open Lean Elab Command Parser Heron

/-- Reprint a syntax node with trailing trivia stripped, then trim whitespace. -/
private def reprintTrimmed (stx : Syntax) : String :=
  (stx.updateTrailing "".toRawSubstring |>.reprint.getD "").trimAscii.toString

/-- Extract doElem array from a doSeq node. -/
private def getDoElems (doSeq : Syntax) : Array Syntax :=
  if doSeq.getKind == ``Term.doSeqBracketed then
    doSeq[1]!.getArgs.map (·[0]!)
  else if doSeq.getKind == ``Term.doSeqIndent then
    doSeq[0]!.getArgs.map (·[0]!)
  else
    #[]

/-- Get the variable name from a doLet's letIdDecl. -/
private def getDoLetVarName? (doLet : Syntax) : Option Name :=
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
private def hasMut (doLet : Syntax) : Bool :=
  doLet.getKind == ``Term.doLet && !doLet[1]!.getArgs.isEmpty

/-- Get the variable name from a doReassign's letIdDecl. -/
private def getReassignVarName? (elem : Syntax) : Option Name :=
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
private partial def collectReassignedVars (elems : Array Syntax) : Std.HashSet Name :=
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

private structure UnusedMutData where
  doLetStx : Syntax
  mutKeyword : Syntax
  replacement : String

/-- Find `let mut x := e` where x is never reassigned in the subsequent do-elements. -/
private def findUnusedMuts (stx : Syntax) : Array UnusedMutData :=
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
            -- Build replacement: reprint the doLet without `mut`
            -- doLet = "let" + optional-mut + letDecl
            -- We want "let" + letDecl (skip the mut)
            let letDecl := elem[2]!
            let mutKw := elem[1]![0]!
            some { doLetStx := elem, mutKeyword := mutKw, replacement := s!"let {reprintTrimmed letDecl}" }
          else none
        | none => none
      else none

@[diagnostic_rule] instance : Diagnostic UnusedMutData where
  ruleName := `unusedMut
  severity := .warning
  detect := fun stx => return findUnusedMuts stx
  hintMessage := fun _ => m!"Remove unnecessary `mut`"
  diagnosticMessage := m!"Remove unused `mut`"
  violationNode := fun fd => fd.mutKeyword
  diagnosticTags := #[.unnecessary]
  replacements := fun fd => #[{
    sourceNode := fd.doLetStx
    targetNode := fd.doLetStx
    insertText := fd.replacement
    sourceLabel := m!"unused mut"
  }]

namespace Tests

-- Unused mut: x is never reassigned
#assertFix unusedMut
  `(doElem| let mut x := 5) => `(doElem| let x := 5) in
example : Nat := Id.run do
  let mut x := 5
  return x + 1

-- Ignore: x IS reassigned
#assertIgnore unusedMut in
example : Nat := Id.run do
  let mut x := 5
  x := x + 1
  return x

-- Ignore: no mut at all
#assertIgnore unusedMut in
example : Nat := Id.run do
  let x := 5
  return x

end Tests
