module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure TupleMatchToSimultaneousMatch where
  matchStx : Syntax
  matchKw : Syntax
  discrElems : Array Syntax
  altsArr : Array Syntax

/-- Extract elements from a `Term.tuple` syntax node `(a, b, ...)`.
Parser: "(" >> optional (term >> ", " >> sepBy1 term ", ") >> ")"
So: [0]="(", [1]=optional-null([0]=first, [1]=",", [2]=sepBy1-null), [2]=")" -/
private meta def getTupleElements? (stx : Syntax) : Option (Array Syntax) :=
  if !stx.isOfKind ``Term.tuple then none
  else
    let opt :=
      stx[1]! -- optional null node

    if opt.getNumArgs < 3 then none
    else
      -- opt[0] = first term, opt[1] = ",", opt[2] = sepBy1 null node
      let first := opt[0]!
      let sepBy := opt[2]!
      let rest := sepBy.getArgs.filter (!·.isAtom)
      some (#[first] ++ rest)

/-- Extract elements from a pattern that is a tuple. -/
private meta def getPatternTupleElements? (stx : Syntax) : Option (Array Syntax) :=
  getTupleElements? stx <|>
    -- Also try anonymous constructor ⟨a, b⟩
    if stx.isOfKind ``Term.anonymousCtor then
      let args := stx[1]!.getArgs.filter (!·.isAtom)
      if args.size >= 2 then some args else none
    else none

/-- Extract the single pattern from a matchAlt, if it has exactly one. -/
private meta def getAltPattern? (alt : Syntax) : Option Syntax := do
  let pats := alt[1]!
  guard (pats.getNumArgs == 1)
  let patGroup := pats[0]!
  guard (patGroup.getNumArgs == 1)
  return patGroup[0]!

/-- Check if a match alt has a tuple pattern of the expected arity (or is a wildcard). -/
private meta def isCompatibleAlt (alt : Syntax) (arity : Nat) : Bool :=
  match getAltPattern? alt with
  | some p =>
    match getPatternTupleElements? p with
    | some elems => elems.size == arity
    | none => p.isOfKind ``Term.hole || (p.isIdent && p.getId == `_)
  | none => false

/-- Reprint a match alt with tuple patterns unwrapped. -/
private meta def reprintAlt (alt : Syntax) : String :=
  let patText :=
    match getAltPattern? alt >>= getPatternTupleElements? with
    | some elems => ", ".intercalate (elems.map reprintTrimmed).toList
    | none =>
      match getAltPattern? alt with
      | some p => reprintTrimmed p
      | none => reprintTrimmed alt[1]!
  s! "| {patText } => {reprintTrimmed alt[3]!}"

private meta instance : Check TupleMatchToSimultaneousMatch where
  name := `tupleMatchToSimultaneous
  kinds := #[``Term.match]
  severity := .warning
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | `(match%$matchKw $discr:term with
          $alts:matchAlt*) =>
      Id.run
        (do
          let some discrElems := getTupleElements? discr |
            return #[]
          let altsArr : Array Syntax := alts.map (·.raw)
          if !altsArr.all (isCompatibleAlt · discrElems.size) then
            return #[]
          return #[{ matchStx := stx, matchKw := matchKw, discrElems, altsArr }])
    | _ => #[]
  message := fun _ => m!"Use simultaneous matching instead of matching on a tuple"
  emphasize := fun m => m.matchStx
  reference := some { topic := "Simultaneous matching", url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ => m!"Matching on `(x, y)` hides the connection between discriminant and pattern from the termination checker. Use `match x, y with` instead."
  replacements := fun m => do
    -- Build replacement text directly: `match x, y with | a, b => ...`
    let discrText := ", ".intercalate (m.discrElems.map reprintTrimmed).toList
    let altTexts := m.altsArr.map fun alt =>
      match getAltPattern? alt >>= getPatternTupleElements? with
      | some patElems =>
        let patText := ", ".intercalate (patElems.map reprintTrimmed).toList
        s!"\n  | {patText} => {reprintTrimmed alt[3]!}"
      | none => s!"\n  {reprintTrimmed alt}"
    let replText := s!"match {discrText} with{String.join altTexts.toList}"
    let env ← getEnv
    match Parser.runParserCategory env `term replText with
    | .ok stx => return #[{
        emphasizedSyntax := m.matchStx
        oldSyntax := m.matchStx
        newSyntax := stx
        inlineViolationLabel := m!"tuple match"
      }]
    | .error _ => return #[]

meta initialize Check.register (α := TupleMatchToSimultaneousMatch)
