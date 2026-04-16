module

public import Lean.Elab.Command

namespace Heron.Rule

open Lean Elab Command

/-- Type-erased rule runner: given syntax, produces LSP `TextEdit`s via
`Rule.detect` + `Rule.replacements` + `Replacement.toTextEdit?`. -/
public meta abbrev TestRunner :=
  Syntax → CommandElabM (Array Lsp.TextEdit)

/-- Registry of rule runners, keyed by rule name. Used by test macros to
invoke rules directly without going through the linter/diagnostic path. -/
public meta initialize testRunnerRegistry : IO.Ref (Std.HashMap Name TestRunner) ←
  IO.mkRef { }

end Heron.Rule
