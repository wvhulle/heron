module

public meta import Heron.Check
meta import Heron.Register
public meta import Heron.Monad

set_option linter.positionalSyntaxAccess false
set_option linter.syntaxKindOrAtomInspection false
set_option linter.syntheticSyntaxConstruction false

open Lean Elab Command Parser Heron

private inductive NatConstructorsToLiteralsMatch where
  | zero (zeroStx : Syntax)
  | succ (appStx : Syntax) (base : Syntax) (succCount : Nat) (needsParens : Bool)
  | unappliedSucc (succStx : Syntax)

private meta def unwrapParens : Syntax → Syntax
  | `(($inner)) => inner
  | stx => stx

private meta partial def peelSuccs (stx : Syntax) (succCount : Nat := 0) : Syntax × Nat :=
  match stx with
  | `(Nat.succ $arg) => peelSuccs (unwrapParens arg) (succCount + 1)
  | _ => (stx, succCount)

private meta def delimitingParentKinds : Array SyntaxNodeKind :=
  #[.anonymous, nullKind, ``Term.paren, ``Term.tuple, ``Term.anonymousCtor, ``Term.typeAscription,
    ``Term.matchAlt, ``Command.declValSimple]

private meta def bindsTighterThanAddition (parentKind : SyntaxNodeKind) : Bool :=
  !delimitingParentKinds.contains parentKind

private structure NatConstructorContext where
  parentKind : SyntaxNodeKind := .anonymous
  insidePattern : Bool := false
  expressionsRewritable : Bool := true

private meta def matchAltPatternsAndRhs? : Syntax → Option (Array Syntax × Syntax)
  | `(Term.matchAltExpr| | $[$patss,*]|* => $rhs) => some (patss.flatMap (·.getElems.map (·.raw)), rhs)
  | _ => none

private meta partial def detectNatConstructors (stx : Syntax) (pos : NatConstructorContext) :
    Array NatConstructorsToLiteralsMatch :=
  let reportable := pos.insidePattern || pos.expressionsRewritable
  let descend (child : Syntax) := detectNatConstructors child { pos with parentKind := stx.getKind }
  match stx with
  | `(Nat.succ $_) =>
    let (base, succCount) := peelSuccs stx
    let here := if reportable then #[.succ stx base succCount (bindsTighterThanAddition pos.parentKind)] else #[]
    here ++ base.getArgs.flatMap fun child => detectNatConstructors child { pos with parentKind := base.getKind }
  | `(Nat.zero) => if reportable then #[.zero stx] else #[]
  | `(Nat.succ) => if reportable && !pos.insidePattern then #[.unappliedSucc stx] else #[]
  | _ =>
    match matchAltPatternsAndRhs? stx with
    | some (patterns, rhs) =>
      patterns.flatMap (detectNatConstructors · { pos with parentKind := .anonymous, insidePattern := true })
        ++ detectNatConstructors rhs { pos with parentKind := stx.getKind, insidePattern := false }
    | none => stx.getArgs.flatMap descend

private meta def statesTheorem (cmd : Syntax) : Bool :=
  (subtreeNodes cmd).any (·.getKind == ``Lean.Parser.Command.theorem)

private meta def literalFor (base : Syntax) (succCount : Nat) : CommandElabM (TSyntax `term) := do
  match base with
  | `(Nat.zero) => `($(Syntax.mkNumLit (toString succCount)):num)
  | `($n:num) => `($(Syntax.mkNumLit (toString (n.getNat + succCount))):num)
  | _ => `($(⟨base⟩) + $(Syntax.mkNumLit (toString succCount)):num)

private meta def isOffsetSum (base : Syntax) : Bool :=
  match base with
  | `(Nat.zero) | `($_:num) => false
  | _ => true

private meta instance : Check NatConstructorsToLiteralsMatch where
  name := `natConstructorsToLiterals
  description := "Suggests `0`, `n + k` and `(· + 1)` instead of `Nat.zero` and `Nat.succ`."
  kinds := #[``Lean.Parser.Command.declaration]
  severity := .information
  category := .style
  detect := fun cmd => pure <|
    detectNatConstructors cmd { expressionsRewritable := !statesTheorem cmd }
  message := fun
    | .zero .. => m!"Use `0` instead of `Nat.zero`"
    | .succ .. => m!"Use `n + 1` instead of `Nat.succ n`"
    | .unappliedSucc .. => m!"Use `(· + 1)` instead of `Nat.succ`"
  emphasize := fun
    | .zero s => s
    | .succ s .. => s
    | .unappliedSucc s => s
  sources := #[.functionalProgrammingInLean "Natural number patterns"
    "Getting-to-Know-Lean/Additional-Conveniences/#natural-number-patterns"]
  explanation := fun
    | .zero .. => m!"`Nat.zero` can be written as the numeric literal `0`, both in patterns and in expressions."
    | .succ .. => m!"`Nat.succ n` can be written as `n + 1`, and nested `Nat.succ` applications as `n + k`. \
                     In a pattern, Lean turns `n + k` back into `Nat.succ` applications, so both forms \
                     match the same values."
    | .unappliedSucc .. => m!"`Nat.succ` used as a function is the same as `(· + 1)`."
  replacements := some fun
    | .zero s => do
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := ← `(0), inlineViolationLabel := m!"Nat.zero → 0" }
      return #[r]
    | .succ s base succCount needsParens => do
      let literal ← literalFor base succCount
      let repl ← if needsParens && isOffsetSum base then `(($literal)) else pure literal
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := repl, inlineViolationLabel := m!"Nat.succ → + 1" }
      return #[r]
    | .unappliedSucc s => do
      let r : Replacement := { emphasizedSyntax := s, oldSyntax := s, newSyntax := ← `((· + 1)), inlineViolationLabel := m!"Nat.succ → (· + 1)" }
      return #[r]

register_check NatConstructorsToLiteralsMatch
