module

meta import Heron.Assert
meta import Heron.Check.TsyntaxRawToTypedAccess

#assertCheck tsyntaxRawToTypedAccess in
def firstRawArg (x : Lean.TSyntax `term) : Lean.Syntax := x.raw.getArg 0

#assertCheck tsyntaxRawToTypedAccess in
def firstRawArgParenthesized (x : Lean.TSyntax `term) : Lean.Syntax := (x).raw.getArg 0

#assertCheck tsyntaxRawToTypedAccess in
def firstRawArgIndexed (x : Lean.TSyntax `term) : Lean.Syntax := x.raw[0]

#assertCheck tsyntaxRawToTypedAccess in
def rawArgs (x : Lean.TSyntax `term) : Array Lean.Syntax :=
  let s := x.raw
  s.getArgs
