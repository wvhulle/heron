/-
Helper used by `GenericExtra.lean` to exercise the *generic* Lean
`recordExtraModUse` path from non-Heron code: a plain command elaborator
that records a module as an implicit dependency, with no rule attribute
or linter involved.

Kept separate from the test so the test's import list is clean.
-/
import Lean.Elab.Command
import Lean.ExtraModUses

open Lean Elab Command

/-- `#recordExtra Mod` records `Mod` as an extra import dependency of the
current file via Lean's standard `recordExtraModUse`. No Heron machinery
involved — stands in for arbitrary third-party metaprogramming. -/
syntax (name := recordExtraCmd) "#recordExtra " ident : command

@[command_elab recordExtraCmd] def elabRecordExtra : CommandElab
  | `(#recordExtra $id) => Lean.recordExtraModUse id.getId (isMeta := false)
  | _ => throwUnsupportedSyntax
