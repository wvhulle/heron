module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure LetBinding where
  ident : TSyntax `ident
  val : TSyntax `term

private structure UnnecessaryIdRunMatch where
  fullStx : Syntax
  lets : Array LetBinding
  finalExpr : TSyntax `term

/-- Match a simple `let $x := $val` doElem. Rejects `let mut`, `let _ ← e`,
`let x : T := e`, and pattern bindings — exactly the shapes that disable the
rewrite. -/
private meta def matchPureLet? : Syntax → Option LetBinding
  | `(doElem| let $x:ident := $val) => some { ident := x, val }
  | _ => none

/-- Match the tail of a pure do-sequence: `return $e` or a bare expression. -/
private meta def matchTail? : Syntax → Option (TSyntax `term)
  | `(doElem| return $e) => some e
  | `(doElem| $e:term) => some e
  | _ => none

/-- Match `Id.run do <doSeq>` where the body is a pure sequence of `let`s
ending in a `return`/bare expression. The antiquotation pattern itself encodes
the whitelist: any imperative doElem fails to match `matchPureLet?` and the
whole rule rejects. The trailing `let x := e; return x` shape is canonicalized
to just `e` so the resulting `UnnecessaryIdRunMatch` represents a single form. -/
private meta def matchUnnecessaryIdRun? (stx : Syntax) : Option UnnecessaryIdRunMatch := do
  let `(Id.run do $seq:doSeq) := stx | none
  let elems := getDoElems seq
  guard !elems.isEmpty
  let lets ← elems.pop.mapM matchPureLet?
  let finalExpr ← matchTail? elems.back!
  let collapsed : Option (Array LetBinding × TSyntax `term) := do
    let last ← lets.back?
    let `($x:ident) := finalExpr | failure
    guard (x.getId == last.ident.getId)
    return (lets.pop, last.val)
  let (lets, finalExpr) := collapsed.getD (lets, finalExpr)
  return { fullStx := stx, lets, finalExpr }

private meta instance : Check UnnecessaryIdRunMatch where
  name := `unnecessaryIdRun
  kinds := #[``Term.app]
  severity := .warning
  category := .simplification
  detect := fun stx => pure <|
    match matchUnnecessaryIdRun? stx with
    | some m => #[m]
    | none => #[]
  message := fun _ => m!"Remove unnecessary `Id.run do`"
  emphasize := fun m => m.fullStx
  reference := some { topic := "`Id.run`", url := "https://leanprover.github.io/functional_programming_in_lean/monad-transformers/do.html#mutable-variables" }
  tags := #[.unnecessary]
  explanation := fun _ => m!"This `Id.run do` block contains no imperative constructs (mutation, loops, early returns). The `do` notation is unnecessary and the expression can be written directly."
  replacements := fun m => do
    let newSyntax ← m.lets.foldrM (init := m.finalExpr) fun b acc =>
      `(let $b.ident := $b.val; $acc)
    return #[{
      emphasizedSyntax := m.fullStx
      oldSyntax := m.fullStx
      newSyntax
      inlineViolationLabel := m!"unnecessary Id.run do"
    }]

meta initialize Check.register (α := UnnecessaryIdRunMatch)
