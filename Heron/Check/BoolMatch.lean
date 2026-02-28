import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure BoolMatchMatch where
  matchStx : Syntax
  matchKw : Syntax
  discr : Syntax
  trueRhs : Syntax
  falseRhs : Syntax
  replacement : String

/-- Extract the pattern text from a matchAlt's pattern node.
matchAlt = "|" pats "=>" rhs, where pats is a null-node of null-nodes of terms. -/
private def altPatText (alt : Syntax) : Option String := do
  let pats := alt[1]!  -- null-node of pattern groups
  guard (pats.getNumArgs == 1)
  let patGroup := pats[0]!  -- null-node of terms in this group
  guard (patGroup.getNumArgs == 1)
  return reprintTrimmed patGroup[0]!

private def findBoolMatch : Syntax → Array BoolMatchMatch :=
  Syntax.collectAll fun stx =>
    if stx.getKind != ``Term.match then #[]
    else
      let discrs := stx[3]!  -- null-node of matchDiscr
      if discrs.getNumArgs != 1 then #[]
      else
        let matchKw := stx[0]!  -- "match" keyword atom
        let discr := discrs[0]![1]!  -- matchDiscr[1] = the expression
        let matchAlts := stx[5]!  -- matchAlts node
        let alts := matchAlts[0]!.getArgs  -- array of matchAlt
        if alts.size != 2 then #[]
        else
          let rhs1 := alts[0]![3]!
          let rhs2 := alts[1]![3]!
          match altPatText alts[0]!, altPatText alts[1]! with
          | some "true", some "false" =>
            let repl := s!"if {reprintTrimmed discr} then {reprintTrimmed rhs1} else {reprintTrimmed rhs2}"
            #[{ matchStx := stx, matchKw, discr, trueRhs := rhs1, falseRhs := rhs2, replacement := repl }]
          | some "false", some "true" =>
            let repl := s!"if {reprintTrimmed discr} then {reprintTrimmed rhs2} else {reprintTrimmed rhs1}"
            #[{ matchStx := stx, matchKw, discr, trueRhs := rhs2, falseRhs := rhs1, replacement := repl }]
          | _, _ => #[]

@[check_rule] instance : Check BoolMatchMatch where
  ruleName := `boolMatch
  severity := .warning
  category := .simplification
  detect := fun stx => return findBoolMatch stx
  message := fun _ => m!"Use `if ... then ... else ...` instead of matching on `Bool`"
  node := fun m => m.matchKw
  tags := #[.unnecessary]
  reference := some { topic := "Bool conditionals", url := "https://lean-lang.org/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ => m!"Pattern matching on `true`/`false` can be written as `if ... then ... else ...`, which is more concise and idiomatic."
  replacements := fun m => #[{
    sourceNode := m.matchStx
    targetNode := m.matchStx
    insertText := m.replacement
    sourceLabel := m!"bool match"
  }]

namespace Tests

#assertCheck boolMatch in
def f (b : Bool) : Nat := match b with | true => 1 | false => 0
becomes `(command| def f (b : Bool) : Nat := if b then 1 else 0)

#assertCheck boolMatch in
def g (b : Bool) : Nat := match b with | false => 0 | true => 1
becomes `(command| def g (b : Bool) : Nat := if b then 1 else 0)

#assertIgnore boolMatch in
def h (n : Nat) : Nat := match n with | 0 => 1 | _ => 2

#assertIgnore boolMatch in
def k (n : Nat) : Nat := match n with | 0 => 1 | 1 => 2 | _ => 3

end Tests
