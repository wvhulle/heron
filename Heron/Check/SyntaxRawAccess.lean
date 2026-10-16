module

public meta import Heron.Check

open Lean Elab Command Parser Heron

private structure SyntaxRawAccessMatch where
  fullStx : Syntax

private meta def isRawAccessSyntax : Syntax → Bool
  | `(($_:term).raw) => true
  | `($x:ident) => isDottedAccess `raw x.getId
  | _ => false

private meta instance : Check SyntaxRawAccessMatch where
  name := `syntaxRawAccess
  kinds := #[``Term.proj, identKind]
  severity := .information
  category := .style
  detect := fun stx => do
    unless isRawAccessSyntax stx do return #[]
    unless ← elaboratesToApplicationOf stx ``Lean.TSyntax.raw do return #[]
    return #[{ fullStx := stx }]
  message := fun _ => m!"Avoid `.raw` on `TSyntax` — use a typed pattern or method instead"
  emphasize := fun m => m.fullStx
  reference := some
    { topic := "TSyntax"
      url := "https://leanprover-community.github.io/lean4-metaprogramming-book/main/06_macros.html" }
  explanation := fun _ =>
    m!"Reaching for `.raw` discards the syntax category bound by `TSyntax`, opening the door to \
       brittle positional indexing or untyped equality on the underlying `Syntax`. Most uses are \
       replaceable by:\n\
       • a `:ident`/`:term`/category-constrained antiquotation in the surrounding pattern, which \
       eliminates the need for `.raw.isIdent` / `.raw.getId` guards;\n\
       • a method that already exists on `TSyntax` (e.g. `TSyntax.getId` for idents);\n\
       • the `BEq` instance on `TSyntax`, instead of comparing `.raw == .raw`.\n\
       Genuinely-needed downcasts to call stdlib APIs that only accept `Syntax` (e.g. \
       `Syntax.getPos?`, `mkNullNode`) are the rare legitimate exception — disable this rule \
       at the call site with `set_option linter.syntaxRawAccess false in`."
  replacements := fun _ => return #[]

meta initialize Check.register (α := SyntaxRawAccessMatch)
