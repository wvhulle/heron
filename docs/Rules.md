# Rules

Heron has two kinds of rules:

- **Checks** run on every command once `linter.heron` is on. Each one underlines the code it
  flags and, for most checks, offers a quick fix that applies the rewrite shown below. Its
  diagnostics carry the code `heron.<rule>`.
- **Refactors** never flag anything. They appear in the editor's code-action menu when the
  selection or cursor is on code they can rewrite.

Every example below is taken from the rule's own tests in `Heron/Check/<Rule>/Detects.lean` or
`Heron/Refactor/<Rule>/Detects.lean`, which check on every build that the rule turns the first
snippet into the second.

Rules based on a book, style guide or another linter name it as their source.

## Turning rules off

Turn a rule off with `set_option linter.<rule> false` in a file, or ``⟨`linter.<rule>, false⟩``
in `leanOptions`.

The checks were renamed to longer, descriptive names (for example `funToCdot` is now
`singleUseLambdaToCdotFunction`); the `linter.<rule>` options with the old names no longer exist.

## Checks

### `adjacentGetSetToModify`

Suggests `modify` instead of `get` directly followed by `set`.

Source: [Functional Programming in Lean: State](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/A-Monad-Construction-Kit/#state-monad)

```lean
def inc : StateM MyState Unit := do
  let s ← get
  set { s with count := s.count + 1 }
```

becomes

```lean
def inc : StateM MyState Unit := do
  modify fun s => { s with count := s.count + 1 }
```

### `lambdaMatchToPatternMatchingLambda`

Suggests `fun | …` pattern-matching syntax instead of a lambda whose body only matches on its
argument.

Source: [Functional Programming in Lean: Anonymous functions](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#anonymous-functions)

```lean
def f := fun x =>
  match x with
  | 0 => "zero"
  | _ => "other"
```

becomes

```lean
def f := fun
  | 0 => "zero"
  | _ => "other"
```

### `lambdaSymbolToFun`

Suggests `fun` instead of `λ`.

Sources: [Functional Programming in Lean: Anonymous functions](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#anonymous-functions),
[Lean standard library style guide: Notation and Unicode](https://github.com/leanprover/lean4/blob/master/doc/std/style.md#notation-and-unicode),
[Mathlib style guide: Anonymous functions](https://leanprover-community.github.io/contribute/style.html#anonymous-functions).
Mathlib's `linter.style.lambdaSyntax` flags the same code without a fix.

```lean
def increment : Nat → Nat := λ x => x + 1
```

becomes

```lean
def increment : Nat → Nat := fun x => x + 1
```

### `matchOnBoolToIfThenElse`

Suggests `if … then … else …` instead of matching on a `Bool`.

Source: [hlint: case a of {True -> t; False -> f} ==> if a then t else f](https://github.com/ndmitchell/hlint/blob/master/data/hlint.yaml)

```lean
def f (b : Bool) : Nat :=
  match b with
  | true => 1
  | false => 0
```

becomes

```lean
def f (b : Bool) : Nat :=
  if b then 1 else 0
```

### `matchOnParametersToPatternMatchingDefinition`

Suggests a pattern-matching definition instead of naming parameters only to `match` on them.

Source: [Functional Programming in Lean: Pattern-matching definitions](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#pattern-matching-definitions)

```lean
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _ => false
```

becomes

```lean
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false
```

### `mergeBindersWithSameType`

Suggests merging adjacent binders that have the same type.

Source: [Functional Programming in Lean: Shared binders](https://lean-lang.org/functional_programming_in_lean/Monads/Additional-Conveniences/#shared-argument-types)

```lean
def f (x : Nat) (y : Nat) := x + y
```

becomes

```lean
def f (x y : Nat) := x + y
```

### `mergeConsecutiveIntros`

Suggests merging consecutive `intro` tactics.

```lean
example : Nat → Nat → True := by intro a; intro b; exact trivial
```

becomes

```lean
example : Nat → Nat → True := by intro a b; exact trivial
```

### `mergeMatchArmsWithSameBody`

Suggests merging match arms whose right-hand sides are identical.

Source: [Functional Programming in Lean: Or-patterns](https://lean-lang.org/functional_programming_in_lean/Monads/Additional-Conveniences/#or-patterns)

```lean
def f (x : Bool) : Nat :=
  match x with
  | true => 1
  | false => 1
```

becomes

```lean
def f (x : Bool) : Nat :=
  match x with
  | true | false => 1
```

### `natConstructorsToLiterals`

Suggests `0`, `n + k` and `(· + 1)` instead of `Nat.zero` and `Nat.succ`.

Source: [Functional Programming in Lean: Natural number patterns](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#natural-number-patterns)

```lean
def f (n : Nat) : Nat := match n with
  | Nat.zero => 0
  | Nat.succ k => k
```

becomes

```lean
def f (n : Nat) : Nat := match n with
  | 0 => 0
  | k + 1 => k
```

### `negatedIfToUnless`

Suggests `unless` instead of `if not` without an `else` branch.

Sources: [Functional Programming in Lean: unless](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#single-branched-if),
[hlint: when (not x) ==> unless x](https://github.com/ndmitchell/hlint/blob/master/data/hlint.yaml)

```lean
example : IO Unit := do
  if not true then
    IO.println "hello"
```

becomes

```lean
example : IO Unit := do
  unless true do
    IO.println "hello"
```

### `nestedExceptToExceptTransformer`

Suggests `ExceptT` instead of nesting `Except` inside another monad in a signature. The quick fix
is only offered when the rewritten definition still elaborates.

Source: [Functional Programming in Lean: Monad transformers](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/A-Monad-Construction-Kit/#exceptions)

```lean
def parseConfig (path : String) (strict : Bool) : IO (Except (List String) Nat) := sorry
```

becomes

```lean
def parseConfig (path : String) (strict : Bool) : ExceptT (List String) IO Nat := sorry
```

### `nestedExprAppToMkAppN`

Suggests `mkAppN` instead of nested `Expr.app`.

Source: [Metaprogramming in Lean 4: Expressions](https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html)

```lean
def f (a b : Lean.Expr) :=
  Expr.app (Expr.app a a) b
```

becomes

```lean
def f (a b : Lean.Expr) :=
  mkAppN a #[a, b]
```

### `nestedOptionToOptionTransformer`

Suggests `OptionT` instead of nesting `Option` inside another monad in a signature. The quick fix
is only offered when the rewritten definition still elaborates.

Source: [Functional Programming in Lean: Monad transformers](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/A-Monad-Construction-Kit/#OptionT)

```lean
def tryLookup {α : Type} (table : List (String × α)) (key : String) : IO (Option α) := sorry
```

becomes

```lean
def tryLookup {α : Type} (table : List (String × α)) (key : String) : OptionT IO α := sorry
```

### `qualifiedConstructorToLeadingDot`

Suggests `.leaf` instead of `BinTree.leaf` where the expected type is known.

Source: [Functional Programming in Lean: Leading dot notation](https://lean-lang.org/functional_programming_in_lean/Monads/Additional-Conveniences/#leading-dot-notation)

```lean
def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)
```

becomes

```lean
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
```

### `removeElsePureUnit`

Suggests dropping a redundant `else pure ()`.

Source: [Functional Programming in Lean: Single-branched if](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#single-branched-if)

```lean
example : IO Unit := do
  if true then
    IO.println "hello"
  else
    pure ()
```

becomes

```lean
example : IO Unit := do
  if true then
    IO.println "hello"
```

### `removeIdRunWithoutEffects`

Suggests removing an `Id.run do` block that uses no effects.

Source: [Functional Programming in Lean: `Id.run`](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#let-mut)

```lean
example : Nat := Id.run do return 42
```

becomes

```lean
example : Nat := 42
```

### `removeLetWildcardOnUnitAction`

Suggests dropping `let _ ←` before an action that returns `Unit`.

```lean
example : IO Unit := do
  let _ ← IO.println "hello"
  pure ()
```

becomes

```lean
example : IO Unit := do
  IO.println "hello"
  pure ()
```

### `removeMutWithoutReassignment`

Suggests removing `mut` from a variable that is never reassigned.

Source: [Functional Programming in Lean: `let mut`](https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/More-do-Features/#let-mut)

```lean
example : Nat := Id.run do
  let mut x := 5
  return x + 1
```

becomes

```lean
example : Nat := Id.run do
  let x := 5
  return x + 1
```

### `singleUseBindToNestedAction`

Suggests a nested action `(← act)` instead of `let x ← act` when `x` is used once, in the next
statement.

Source: [Functional Programming in Lean: Nested actions](https://lean-lang.org/functional_programming_in_lean/Monads/do--Notation-for-Monads/)

```lean
def mapM' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM' f xs
    pure (hd :: tl)
```

becomes

```lean
def mapM' [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    pure (hd :: (← mapM' f xs))
```

### `singleUseLambdaToCdotFunction`

Suggests `·` instead of an explicit lambda whose parameter is used once.

Sources: [Functional Programming in Lean: Centered dot](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#anonymous-functions),
[Mathlib style guide: Anonymous functions](https://leanprover-community.github.io/contribute/style.html#anonymous-functions)

```lean
def f :=
  List.map (fun x => x + 1) [1, 2, 3]
```

becomes

```lean
def f :=
  List.map (· + 1) [1, 2, 3]
```

### `stringConcatenationToInterpolation`

Flags `"…" ++ toString x ++ "…"` and suggests an interpolated `s!"…{x}…"` string instead. It
offers no automatic fix.

Source: [Functional Programming in Lean: String interpolation](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#string-interpolation)

```lean
def describe (n : Nat) : String := "three fives is " ++ toString (n * 3)
```

### `syntaxKindComparisonToQuotationPattern`

Flags a `Syntax.getKind` comparison followed by positional child access such as `getArg`, and
suggests matching with an antiquotation pattern instead. It offers no automatic fix.

Source: [Metaprogramming in Lean 4: Syntax pattern matching](https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html#matching-on-syntax)

```lean
def firstArg (stx : Lean.Syntax) : Lean.Syntax :=
  if stx.getKind == ``Lean.Parser.Term.app then stx.getArg 0 else stx
```

### `tsyntaxRawToTypedAccess`

Flags `.raw` on a `TSyntax` followed by positional child access, and suggests a typed pattern
instead. It offers no automatic fix.

Source: [Metaprogramming in Lean 4: Typed syntax](https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html#typed-syntax)

```lean
def firstRawArg (x : Lean.TSyntax `term) : Lean.Syntax := x.raw.getArg 0
```

### `tupleMatchToSimultaneousMatch`

Suggests matching on several values at once instead of matching on a tuple.

Source: [Functional Programming in Lean: Simultaneous matching](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#simultaneous-matching)

```lean
def f (x y : Nat) : Nat :=
  match (x, y) with
  | (a, b) => a + b
```

becomes

```lean
def f (x y : Nat) : Nat :=
  match x, y with
  | a, b => a + b
```

### `wildcardMatchToIfLet`

Suggests `if let` instead of a two-arm `match` whose second arm is a wildcard.

Source: [Functional Programming in Lean: if let](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/Additional-Conveniences/#if-let)

```lean
def f (x : Option Nat) : Nat := match x with | some v => v | _ => 0
```

becomes

```lean
def f (x : Option Nat) : Nat := if let some v := x then v else 0
```

## Refactors

### `bindToDo`

Rewrites `>>=` into do-notation.

Source: [Functional Programming in Lean: do-notation for monads](https://lean-lang.org/functional_programming_in_lean/Monads/do--Notation-for-Monads/)

```lean
def f := IO.getLine >>= fun s => IO.println s
```

becomes

```lean
def f := do
  let s ← IO.getLine
  IO.println s
```

### `flipIf`

Swaps the branches of an `if` and negates its condition.

```lean
def flipMe (p : Bool) (a b : Nat) : Nat := if !p then a else b
```

becomes

```lean
def flipMe (p : Bool) (a b : Nat) : Nat := if p then b else a
```

### `inline`

Inlines one use of a definition or `let` binding. With `def double (n : Nat) := n + n`:

```lean
example : Nat := double 3
```

becomes

```lean
example : Nat := (3 + 3)
```

### `inlineAllConst`

Inlines every use of a private definition and removes the definition. It is offered on the
definition's name. With `private def triple (n : Nat) := n + n + n`:

```lean
example : Nat :=
  triple 2 + triple 3
```

becomes

```lean
example : Nat :=
  (2 + 2 + 2) + (3 + 3 + 3)
```
