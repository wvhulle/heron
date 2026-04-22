module

meta import DeadHeron.Assert
-- A rule-providing module with its linter NOT enabled — the import
-- is genuinely unused and must still be flagged.
meta import Heron.Check.BoolMatchToIf
-- A non-rule module that is also genuinely unused.
meta import Lean.Data.Json.Parser

-- Assert both genuinely unused imports are still detected. This regression
-- guard ensures the fix for the rule-module false positive does not
-- over-correct by marking all rule modules as used regardless of whether
-- their linter is actually enabled.
#assertImports unused := [Heron.Check.BoolMatchToIf, Lean.Data.Json.Parser]
