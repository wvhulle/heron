module

meta import Heron.Assert
meta import DevExecutables.SelfLint.PositionalSyntaxAccess

#assertIgnore positionalSyntaxAccess in
def swapPair : Lean.Syntax → Lean.MacroM Lean.Syntax
  | `(($a, $b)) => `(($b, $a))
  | _ => Lean.Macro.throwUnsupported

private structure Call where
  args : Array Nat

private def Call.getArg (c : Call) (i : Nat) : Nat := c.args.getD i 0

#assertIgnore positionalSyntaxAccess in
example (c : Call) : Nat := c.getArg 0

#assertIgnore positionalSyntaxAccess in
example (xs : Array Nat) : Nat := xs[0]!
