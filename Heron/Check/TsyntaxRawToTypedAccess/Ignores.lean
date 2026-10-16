module

meta import Heron.Assert
meta import Heron.Check.TsyntaxRawToTypedAccess

-- Field named `raw` on a user struct, not a TSyntax escape hatch.
private structure Box where
  raw : Nat

#assertIgnore tsyntaxRawToTypedAccess in
example (b : Box) : Nat := b.raw + 1

#assertIgnore tsyntaxRawToTypedAccess in
def parenthesizedBoxField (b : Box) : Nat := (b).raw + 1

#assertIgnore tsyntaxRawToTypedAccess in
example (x : Lean.TSyntax `term) : Lean.Syntax := (x).raw

#assertIgnore tsyntaxRawToTypedAccess in
example (x : Lean.TSyntax `term) : Lean.Syntax := x.raw

#assertIgnore tsyntaxRawToTypedAccess in
instance : Coe (Lean.TSyntax `ident) (Lean.TSyntax `term) where
  coe s := ⟨s.raw⟩

#assertIgnore tsyntaxRawToTypedAccess in
def kindOf (c : Lean.TSyntax `command) : Lean.Name := c.raw.getKind
