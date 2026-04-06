import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure TupleMatchMatch where
  matchStx : Syntax
  matchKw : Syntax
  replacement : String

/-- Extract elements from a `Term.tuple` syntax node `(a, b, ...)`.
Parser: "(" >> optional (term >> ", " >> sepBy1 term ", ") >> ")"
So: [0]="(", [1]=optional-null([0]=first, [1]=",", [2]=sepBy1-null), [2]=")" -/
private def getTupleElements? (stx : Syntax) : Option (Array Syntax) :=
  if !stx.isOfKind ``Term.tuple then none
  else
    let opt := stx[1]!  -- optional null node
    if opt.getNumArgs < 3 then none
    else
      -- opt[0] = first term, opt[1] = ",", opt[2] = sepBy1 null node
      let first := opt[0]!
      let sepBy := opt[2]!
      let rest := sepBy.getArgs.filter (!·.isAtom)
      some (#[first] ++ rest)

/-- Extract elements from a pattern that is a tuple. -/
private def getPatternTupleElements? (stx : Syntax) : Option (Array Syntax) :=
  getTupleElements? stx <|>
  -- Also try anonymous constructor ⟨a, b⟩
  if stx.isOfKind ``Term.anonymousCtor then
    let args := stx[1]!.getArgs.filter (!·.isAtom)
    if args.size >= 2 then some args else none
  else none

/-- Extract the single pattern from a matchAlt, if it has exactly one. -/
private def getAltPattern? (alt : Syntax) : Option Syntax := do
  let pats := alt[1]!
  guard (pats.getNumArgs == 1)
  let patGroup := pats[0]!
  guard (patGroup.getNumArgs == 1)
  return patGroup[0]!

/-- Check if a match alt has a tuple pattern of the expected arity (or is a wildcard). -/
private def isCompatibleAlt (alt : Syntax) (arity : Nat) : Bool :=
  match getAltPattern? alt with
  | some p =>
    match getPatternTupleElements? p with
    | some elems => elems.size == arity
    | none => p.isOfKind ``Term.hole || (p.isIdent && p.getId == `_)
  | none => false

/-- Reprint a match alt with tuple patterns unwrapped. -/
private def reprintAlt (alt : Syntax) : String :=
  let patText := match getAltPattern? alt >>= getPatternTupleElements? with
    | some elems => ", ".intercalate (elems.map reprintTrimmed).toList
    | none => match getAltPattern? alt with
      | some p => reprintTrimmed p
      | none => reprintTrimmed alt[1]!
  s!"| {patText} => {reprintTrimmed alt[3]!}"

private def findTupleMatches : Syntax → Array TupleMatchMatch :=
  Syntax.collectAll fun
    | stx@`(match $discr:term with $alts:matchAlt*) => Id.run do
      let some discrElems := getTupleElements? discr | return #[]
      let altsArr : Array Syntax := alts.map (·.raw)
      if !altsArr.all (isCompatibleAlt · discrElems.size) then return #[]
      let discrText := ", ".intercalate (discrElems.map reprintTrimmed).toList
      let altsText := "\n  ".intercalate (altsArr.map reprintAlt).toList
      return #[{ matchStx := stx, matchKw := stx[0]!,
                 replacement := s!"match {discrText} with\n  {altsText}" }]
    | _ => #[]

@[check_rule] instance : Check TupleMatchMatch where
  ruleName := `tupleMatch
  severity := .warning
  category := .simplification
  pureDetect := findTupleMatches
  message := fun _ => m!"Use simultaneous matching instead of matching on a tuple"
  node := fun m => m.matchStx
  reference := some { topic := "Simultaneous matching", url := "https://lean-lang.org/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ => m!"Matching on `(x, y)` hides the connection between discriminant and pattern from the termination checker. Use `match x, y with` instead."
  replacements := fun m => #[{
    sourceNode := m.matchStx
    targetNode := m.matchStx
    insertText := m.replacement
    sourceLabel := m!"tuple match"
  }]

namespace Tests

#assertCheck tupleMatch in
def f (x y : Nat) : Nat := match (x, y) with | (a, b) => a + b
becomes `(command| def f (x y : Nat) : Nat := match x, y with
  | a, b => a + b)

#assertIgnore tupleMatch in
def g (x y : Nat) : Nat := match x, y with | a, b => a + b

#assertIgnore tupleMatch in
def h (p : Nat × Nat) : Nat := match p with | (a, b) => a + b

end Tests
