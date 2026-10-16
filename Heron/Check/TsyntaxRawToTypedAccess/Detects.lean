module

meta import Heron.Assert
meta import Heron.Check.TsyntaxRawToTypedAccess

#assertCheck tsyntaxRawToTypedAccess in
example (x : Lean.TSyntax `term) : Lean.Syntax := (x).raw

#assertCheck tsyntaxRawToTypedAccess in
example (x : Lean.TSyntax `term) : Lean.Syntax := x.raw
