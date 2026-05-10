module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure TupleAlt where
  /-- Original alt syntax (used as the replacement-target span). -/
  stx : TSyntax ``Term.matchAlt
  /-- Either the unwrapped tuple element patterns, or `none` for a wildcard. -/
  pats : Option (Array (TSyntax `term))
  rhs : TSyntax `term

private structure TupleMatchToSimultaneousMatch where
  matchStx : Syntax
  matchKw : Syntax
  discrElems : Array (TSyntax `term)
  alts : Array TupleAlt

/-- Match a tuple expression `(a, b, ...)` with at least two elements. -/
private meta def tupleElems? : TSyntax `term → Option (Array (TSyntax `term))
  | `(($x, $xs,*)) => some (#[x] ++ xs.getElems)
  | _ => none

/-- Match a pattern that is either a parenthesised tuple `(a, b)` or an
anonymous-constructor tuple `⟨a, b⟩`. -/
private meta def patternTupleElems? (pat : TSyntax `term) : Option (Array (TSyntax `term)) :=
  tupleElems? pat <|> match pat with
    | `(⟨$x, $xs,*⟩) => if xs.getElems.size ≥ 1 then some (#[x] ++ xs.getElems) else none
    | _ => none

/-- Recognise `_` as a wildcard pattern. -/
private meta def isWildcardPattern (pat : TSyntax `term) : Bool :=
  match pat with
  | `(_) => true
  | _ => false

private meta def classifyAlt? (arity : Nat) :
    TSyntax ``Term.matchAlt → Option TupleAlt
  | stx@`(Term.matchAltExpr| | $pat:term => $rhs) =>
    match patternTupleElems? pat with
    | some elems =>
      if elems.size == arity then some { stx, pats := some elems, rhs } else none
    | none =>
      if isWildcardPattern pat then some { stx, pats := none, rhs } else none
  | _ => none

private meta instance : Check TupleMatchToSimultaneousMatch where
  name := `tupleMatchToSimultaneous
  kinds := #[``Term.match]
  severity := .warning
  category := .simplification
  detect := fun stx => pure <|
    match stx with
    | `(match%$matchKw $discr:term with $alts:matchAlt*) =>
      let m? : Option TupleMatchToSimultaneousMatch := do
        let discrElems ← tupleElems? discr
        let alts ← alts.mapM (classifyAlt? discrElems.size)
        return { matchStx := stx, matchKw, discrElems, alts }
      m?.toArray
    | _ => #[]
  message := fun _ => m!"Use simultaneous matching instead of matching on a tuple"
  emphasize := fun m => m.matchStx
  reference := some { topic := "Simultaneous matching", url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ => m!"Matching on `(x, y)` hides the connection between discriminant and pattern from the termination checker. Use `match x, y with` instead."
  replacements := fun m => do
    let discrs : TSyntaxArray `term := m.discrElems
    let arity := m.discrElems.size
    let newAlts ← m.alts.mapM fun a => do
      let pats : TSyntaxArray `term ← match a.pats with
        | some pats => pure pats
        | none => (Array.replicate arity ·) <$> `(_)
      `(Term.matchAltExpr| | $pats,* => $a.rhs)
    let repl ← `(match $[$discrs:term],* with $newAlts:matchAlt*)
    return #[{
      emphasizedSyntax := m.matchStx
      oldSyntax := m.matchStx
      newSyntax := repl
      inlineViolationLabel := m!"tuple match"
    }]

meta initialize Check.register (α := TupleMatchToSimultaneousMatch)
