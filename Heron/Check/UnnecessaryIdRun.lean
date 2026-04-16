import Heron.Check

open Lean Elab Command Parser Term Heron

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

/-- Build the replacement syntax for a pure do sequence.
Extracts the final expression and any let bindings, converting
`do let x := e; return x` → `e` and `do let x := e; body` → `let x := e\nbody`. -/
private def buildReplacement? (elems : Array Syntax) : Option (Array Syntax × Syntax) := do
  guard !elems.isEmpty
  let last := elems.back!
  let finalExpr ←
    if last.getKind == ``doReturn then getReturnExpr? last
    else if last.getKind == ``doExpr then some last[0]!
    else none
  let inits := elems.pop
  if inits.isEmpty then
    return (#[], finalExpr)
  match getLetVarName? inits.back!, getLetRhs? inits.back! with
  | some varName, some rhs =>
    if finalExpr.isIdent && finalExpr.getId == varName then
      return (inits.pop, rhs)
    else return (inits, finalExpr)
  | _, _ => return (inits, finalExpr)

private structure UnnecessaryIdRunMatch where
  fullStx : Syntax
  idRunDoSpan : Syntax
  elems : Array Syntax

private def findUnnecessaryIdRun : Syntax → Array UnnecessaryIdRunMatch :=
  Syntax.collectAll fun stx =>
    match isIdRunDo? stx with
    | some (fullStx, idRunDoSpan, doSeq) =>
      let elems := getDoElems doSeq
      if isPureDoSeq elems then
        #[{ fullStx, idRunDoSpan, elems }]
      else #[]
    | none => #[]

@[check_rule] instance : Check UnnecessaryIdRunMatch where
  name := `unnecessaryIdRun
  severity := .warning
  category := .simplification
  find := findUnnecessaryIdRun
  message := fun _ => m!"Remove unnecessary `Id.run do`"
  emphasize := fun m => m.idRunDoSpan
  reference := some { topic := "`Id.run`", url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/do.html#mutable-variables" }
  tags := #[.unnecessary]
  explanation := fun _ => m!"This `Id.run do` block contains no imperative constructs (mutation, loops, early returns). The `do` notation is unnecessary and the expression can be written directly."
  replacements := fun m => do
    let some (letBindings, finalExpr) := buildReplacement? m.elems | return #[]
    -- Reconstruct: let bindings followed by final expression
    -- For single expression: just the expression
    -- For let + expr: use let-in chain
    let mut result : TSyntax `term := ⟨finalExpr⟩
    for binding in letBindings.reverse do
      -- Extract ident and RHS from the doLet's letIdDecl
      let inner := binding[2]![0]!  -- letIdDecl
      let ident : TSyntax `ident := ⟨inner[0]![0]!⟩
      let val : TSyntax `term := ⟨inner[4]!⟩
      result ← `(let $ident := $val; $result)
    return #[{
      emphasizedSyntax := m.fullStx
      oldSyntax := m.fullStx
      newSyntax := result
      inlineViolationLabel := m!"unnecessary Id.run do"
    }]
