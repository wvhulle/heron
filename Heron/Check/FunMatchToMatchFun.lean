import Heron.Check
import Heron.Assert

open Lean Elab Command Parser Heron

private structure FunMatchToMatchFunMatch where
  funStx : Syntax
  matchAlts : Syntax

/-- Detect `fun x => match x with | ...` where x is the sole parameter
and the body is immediately a match on exactly that parameter. -/
private def detectFunMatch? : Syntax → Option FunMatchToMatchFunMatch
  | stx@`(fun $x:ident => match $discr:term with $alts:matchAlts) =>
    if discr.raw.isIdent && discr.raw.getId == x.getId then
      some { funStx := stx, matchAlts := alts }
    else none
  | _ => none

private def findFunMatchToMatchFun (stx : Syntax) : Array FunMatchToMatchFunMatch :=
  Syntax.collectAll
    (fun s =>
      match detectFunMatch? s with
      | some m => #[m]
      | none => #[])
    stx

@[check_rule]
instance : Check FunMatchToMatchFunMatch where
  name := `funMatchToMatchFun
  severity := .information
  category := .simplification
  find := findFunMatchToMatchFun
  message := fun _ => m!"Use `fun | ...` pattern matching syntax"
  emphasize := fun m => m.funStx
  reference :=
    some
      { topic := "Anonymous functions",
        url := "https://leanprover.github.io/functional_programming_in_lean/getting-to-know/conveniences.html" }
  explanation := fun _ =>
    m!"`fun x => match x with | ...` can be simplified to `fun | ...` using Lean's pattern matching lambda syntax."
  replacements := fun m => do
    let alts : TSyntax ``Term.matchAlts := ⟨m.matchAlts⟩
    let repl ← `(fun$alts:matchAlts)
    return #[{
          emphasizedSyntax := m.funStx
          oldSyntax := m.funStx
          newSyntax := repl
          inlineViolationLabel := m!"fun match → fun |" }]

namespace Tests

#assertCheck funMatchToMatchFun in
  def f := fun x =>
    match x with
    | 0 => "zero"
    | _ => "other" becomes
  `(def f := fun
      | 0 => "zero"
      | _ => "other")

-- Ignore: multiple parameters
#assertIgnore funMatchToMatchFun in
  def g := fun x y =>
    match x with
    | 0 => y
    | _ =>
      0

-- Ignore: match on different variable
#assertIgnore funMatchToMatchFun in
  def h (y : Nat) := fun x =>
    match y with
    | 0 => x
    | _ =>
      0

-- Ignore: already using fun | syntax
#assertIgnore funMatchToMatchFun in
  def k := fun
    | 0 => "zero"
    | _ => "other"

end Tests
