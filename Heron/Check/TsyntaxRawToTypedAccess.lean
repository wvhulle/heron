module

public meta import Heron.Check
public meta import Heron.Monad

open Lean Elab Command Parser Heron

private structure TsyntaxRawToTypedAccessMatch where
  fullStx : Syntax

private meta def accessesRawField (fieldPath : List Name) : Bool :=
  fieldPath.any (· == `raw)

private meta def isRawAccessSyntax : Syntax → Bool
  | `(($_:term).$field:ident) => accessesRawField field.getId.components
  | `($x:ident) => accessesRawField (x.getId.components.drop 1)
  | _ => false

private meta def detectRawEscapesBeforePositionalAccess (cmd : Syntax) :
    CommandElabM (Array TsyntaxRawToTypedAccessMatch) := do
  let rawSites := (subtreeNodes cmd).filter isRawAccessSyntax
  if rawSites.isEmpty then return #[]
  unless ← usesPositionalSyntaxAccess cmd do return #[]
  rawSites.filterMapM fun site => do
    unless ← elaboratesMentioningProjection site ``Lean.TSyntax ``Lean.TSyntax.raw do return none
    return some { fullStx := site }

private meta instance : Check TsyntaxRawToTypedAccessMatch where
  name := `tsyntaxRawToTypedAccess
  kinds := #[]
  severity := .information
  category := .style
  detect := detectRawEscapesBeforePositionalAccess
  message := fun _ => m!"Avoid `.raw` on `TSyntax` followed by positional child access — use a typed pattern instead"
  emphasize := fun m => m.fullStx
  reference := some
    { topic := "Typed syntax"
      url := "https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html#typed-syntax" }
  explanation := fun _ =>
    m!"Reaching for `.raw` discards the syntax category bound by `TSyntax`, and this declaration \
       then indexes the underlying `Syntax` by position (`getArg`, `getArgs`, `stx[i]`), which \
       silently breaks when the parser's layout changes. A `:ident`/`:term`/category-constrained \
       antiquotation in a `` `(...) `` pattern binds the same children by name and is checked at \
       compile time. `.raw` itself is fine for `Coe` instances between categories, for \
       `getKind` dispatch, or to call APIs that only accept `Syntax`."
  replacements := fun _ => return #[]

meta initialize Check.register (α := TsyntaxRawToTypedAccessMatch)
