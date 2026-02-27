import Heron.Diagnostic
import Heron.Assert

open Lean Elab Command Parser Term Heron

/-- Reprint a syntax node with trailing trivia stripped, then trim whitespace. -/
private def reprintTrimmed (stx : Syntax) : String :=
  (stx.updateTrailing "".toRawSubstring |>.reprint.getD "").trimAscii.toString

/-- Match `Id.run do <doSeq>`, returning `(fullAppStx, idRunDoSpan, doSeqNode)`. -/
private def isIdRunDo? : Syntax → Option (Syntax × Syntax × Syntax)
  | stx@`($fn $arg) =>
    if fn.raw.isIdent && fn.raw.getId == `Id.run then
      let doBlock := arg.raw
      if doBlock.isOfKind ``Lean.Parser.Term.do then
        let doKw := doBlock[0]!
        let idRunDoSpan := do
          let r1 ← fn.raw.getRange?
          let r2 ← doKw.getRange?
          pure (Syntax.ofRange ⟨r1.start, r2.stop⟩)
        some (stx, idRunDoSpan.getD fn.raw, doBlock[1]!)
      else none
    else none
  | _ => none

/-- Extract doElem array from a doSeq node (doSeqIndent or doSeqBracketed). -/
private def getDoElems (doSeq : Syntax) : Array Syntax :=
  if doSeq.getKind == ``doSeqBracketed then
    doSeq[1]!.getArgs.map (·[0]!)
  else if doSeq.getKind == ``doSeqIndent then
    doSeq[0]!.getArgs.map (·[0]!)
  else
    #[]

/-- Check if a doElem is an imperative construct. -/
private def isImperative (elem : Syntax) : Bool :=
  let k := elem.getKind
  k == ``doFor || k == ``doReassign || k == ``doReassignArrow ||
  k == ``doBreak || k == ``doContinue || k == ``doLetArrow || k == ``doLetRec ||
  k == ``doTry || k == ``doIf || k == ``doMatch || k == ``doUnless ||
  k == ``doNested || k == ``doMatchExpr || k == ``doLetElse || k == ``doLetMetaExpr ||
  k == ``doLetExpr || k == ``doHave || k == ``doDbgTrace || k == ``doAssert ||
  -- doLet with mut
  (k == ``doLet && !elem[1]!.getArgs.isEmpty)

/-- Check if the do sequence is purely non-imperative. -/
private def isPureDoSeq (elems : Array Syntax) : Bool :=
  if elems.isEmpty then false
  else
    let n := elems.size
    (Array.range n).all fun i =>
      let elem := elems[i]!
      let k := elem.getKind
      if isImperative elem then false
      else if k == ``doReturn then i + 1 == n
      else if k == ``doLet then true
      else if k == ``doExpr then i + 1 == n
      else false

/-- Get the variable name from a doLet's letDecl. -/
private def getLetVarName? (doLet : Syntax) : Option Name :=
  if doLet.getKind == ``doLet then
    let letDecl := doLet[2]!  -- doLet[0]="let", [1]=optional mut, [2]=letDecl
    let inner := letDecl[0]!  -- letIdDecl
    if inner.getKind == ``letIdDecl then
      let letId := inner[0]!
      if letId.getKind == ``letId then
        let ident := letId[0]!
        if ident.isIdent then some ident.getId else none
      else none
    else none
  else none

/-- Get the RHS expression from a doLet's letIdDecl. -/
private def getLetRhs? (doLet : Syntax) : Option Syntax :=
  if doLet.getKind == ``doLet then
    let letDecl := doLet[2]!
    let inner := letDecl[0]!
    if inner.getKind == ``letIdDecl then some inner[4]!
    else none
  else none

/-- Get the expression from a doReturn node. -/
private def getReturnExpr? (elem : Syntax) : Option Syntax :=
  if elem.getKind == ``doReturn then
    let optExpr := elem[1]!
    if optExpr.getNumArgs >= 1 then some optExpr[0]!
    else none
  else none

/-- Build the replacement text for a pure do sequence. -/
private def buildReplacement (elems : Array Syntax) : Option String :=
  if elems.isEmpty then none
  else
    let last := elems.back!
    let finalExpr? :=
      if last.getKind == ``doReturn then getReturnExpr? last
      else if last.getKind == ``doExpr then some last[0]!
      else none
    match finalExpr? with
    | none => none
    | some finalExpr =>
      let inits := elems.pop
      if inits.isEmpty then
        some (reprintTrimmed finalExpr)
      else
        -- Try to collapse trailing `let x := rhs; return x` → `rhs`
        let lastInit := inits.back!
        match getLetVarName? lastInit with
        | some varName =>
          if finalExpr.isIdent && finalExpr.getId == varName then
            match getLetRhs? lastInit with
            | some rhs =>
              let parts := (inits.pop.map reprintTrimmed).push (reprintTrimmed rhs)
              some (parts.toList |> "\n".intercalate)
            | none =>
              let parts := (inits.map reprintTrimmed).push (reprintTrimmed finalExpr)
              some (parts.toList |> "\n".intercalate)
          else
            let parts := (inits.map reprintTrimmed).push (reprintTrimmed finalExpr)
            some (parts.toList |> "\n".intercalate)
        | none =>
          let parts := (inits.map reprintTrimmed).push (reprintTrimmed finalExpr)
          some (parts.toList |> "\n".intercalate)

private structure IdRunTrivialData where
  fullStx : Syntax
  idRunDoSpan : Syntax
  replacement : String

private def findIdRunTrivial : Syntax → Array IdRunTrivialData :=
  Syntax.collectAll fun stx =>
    match isIdRunDo? stx with
    | some (fullStx, idRunDoSpan, doSeq) =>
      let elems := getDoElems doSeq
      if isPureDoSeq elems then
        match buildReplacement elems with
        | some repl => #[{ fullStx, idRunDoSpan, replacement := repl }]
        | none => #[]
      else #[]
    | none => #[]

@[diagnostic_rule] instance : Diagnostic IdRunTrivialData where
  ruleName := `idRunTrivial
  severity := .warning
  category := .simplification
  detect := fun stx => return findIdRunTrivial stx
  hintMessage := fun _ => m!"Remove unnecessary `Id.run do`"
  diagnosticMessage := m!"Remove trivial `Id.run do`"
  violationNode := fun fd => fd.idRunDoSpan
  diagnosticTags := #[.unnecessary]
  explanation := fun _ => m!"This `Id.run do` block contains no imperative constructs (mutation, loops, early returns). The `do` notation is unnecessary and the expression can be written directly."
  replacements := fun fd => #[{
    sourceNode := fd.fullStx
    targetNode := fd.fullStx
    insertText := fd.replacement
    sourceLabel := m!"unnecessary Id.run do"
  }]

namespace Tests

-- Simple return
#assertFix idRunTrivial
  `(term| Id.run do return 42) => `(term| 42) in
example : Nat := Id.run do return 42

-- Let + return same variable collapses
#assertFix idRunTrivial
  `(term| Id.run do
  let x := 5
  return x) => `(term| 5) in
example : Nat := Id.run do
  let x := 5
  return x

-- Ignore: has mut (imperative)
#assertIgnore idRunTrivial in
example : Nat := Id.run do
  let mut x := 5
  x := x + 1
  return x

-- Ignore: has for loop
#assertIgnore idRunTrivial in
example : Nat := Id.run do
  let mut sum := 0
  for x in [1, 2, 3] do
    sum := sum + x
  return sum

-- Ignore: has early return (doIf)
#assertIgnore idRunTrivial in
example : Nat := Id.run do
  if true then return 1
  return 2

end Tests
