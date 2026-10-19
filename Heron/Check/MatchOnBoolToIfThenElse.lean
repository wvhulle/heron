module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

set_option linter.positionalSyntaxAccess false

open Lean Elab Command Parser Heron

private structure MatchOnBoolToIfThenElseMatch where
  matchStx : Syntax
  matchKw : Syntax
  discr : TSyntax `term
  trueRhs : TSyntax `term
  falseRhs : TSyntax `term

private meta def boolMatch? : Syntax → Option MatchOnBoolToIfThenElseMatch
  | stx@`(match%$matchKw $discr:term with
      | true => $rhs1:term
      | false => $rhs2:term) =>
    some { matchStx := stx, matchKw, discr, trueRhs := rhs1, falseRhs := rhs2 }
  | stx@`(match%$matchKw $discr:term with
      | false => $rhs1:term
      | true => $rhs2:term) =>
    some { matchStx := stx, matchKw, discr, trueRhs := rhs2, falseRhs := rhs1 }
  | _ => none

private meta def ifThenElse (m : MatchOnBoolToIfThenElseMatch) : CommandElabM (TSyntax `term) :=
  `(if $m.discr then $m.trueRhs else $m.falseRhs)

private meta def detectBoolMatchesWhoseIfRewriteElaborates (cmd : Syntax) :
    CommandElabM (Array MatchOnBoolToIfThenElseMatch) :=
  (subtreeNodes cmd).filterMapM fun node => do
    let some m := boolMatch? node | return none
    let probe := replaceSourceNode cmd m.matchStx (← ifThenElse m)
    unless ← elaboratesWithoutErrorsInProbeNamespace probe do return none
    return some m

private meta instance : Check MatchOnBoolToIfThenElseMatch where
  name := `matchOnBoolToIfThenElse
  description := "Suggests `if … then … else …` instead of matching on a `Bool`."
  kinds := #[]
  wholeCommand := true
  severity := .information
  category := .simplification
  detect := detectBoolMatchesWhoseIfRewriteElaborates
  message := fun _ => m!"Use `if ... then ... else ...` instead of matching on `Bool`"
  emphasize := fun m => m.matchKw
  tags := #[.unnecessary]
  sources := #[.hlint "case a of {True -> t; False -> f} ==> if a then t else f"]
  explanation := fun _ =>
    m!"Pattern matching on `true`/`false` can be written as `if ... then ... else ...`, which is \
       more concise. The rewrite is only offered where it type-checks: when the result type \
       depends on the matched `Bool`, `match` is needed to refine it in each branch."
  replacements := some fun m => do
    return #[{
          emphasizedSyntax := m.matchStx
          oldSyntax := m.matchStx
          newSyntax := ← ifThenElse m
          inlineViolationLabel := m!"bool match" }]

register_check MatchOnBoolToIfThenElseMatch
