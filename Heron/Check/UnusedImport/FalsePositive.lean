import Heron.Assert
import Heron.Check.BoolMatchToIf

-- Reference a constant from `Heron.Assert` so it is counted as used via
-- the usual constant-reference analysis.
private def _used := @Heron.Assert.applyEdits

-- Enable the `boolMatchToIf` linter — this rule is provided by the
-- `Heron.Check.BoolMatchToIf` import. Without the extra-mod-use tracking,
-- the analysis has no way to know the import is needed, since no constant
-- from it is referenced in this file.
set_option linter.boolMatchToIf true

-- Assert that `Heron.Check.BoolMatchToIf` is NOT flagged as unused.
-- This test guards against the false-positive where rule-providing
-- imports (activated purely via `@[init]` side-effects) are treated
-- as unused because `computeNeeds` only tracks constant references.
#assertImports unused := []
