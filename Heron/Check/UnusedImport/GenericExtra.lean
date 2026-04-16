/-
Regression test for the *generic* `Lean.recordExtraModUse` path.

Demonstrates that unused-import detection picks up implicit dependencies
from arbitrary non-Heron metaprogramming (i.e. any code using Lean's
documented `recordExtraModUse` API), not just from Heron's rule registry.

`ExtraModUseUmbrella` re-exports a test-only leaf that is unreachable
from any other direct import, so the umbrella is the unique cover for
the recorded extra `Heron.Check.UnusedImport.ExtraModUseLeaf` and must
be kept. `Lean.Data.PersistentHashMap` is genuinely unused and must be
flagged.
-/
import Heron.Assert
import Heron.Check.UnusedImport.ExtraModUseHelper
import Heron.Check.UnusedImport.ExtraModUseUmbrella
import Lean.Data.PersistentHashMap

-- Force direct-hit coverage for the `Heron.Assert` and helper imports
-- (their value comes from side-effect registration, not from references).
private def _usedAssert := @Heron.Assert.applyEdits
private def _usedHelper := @elabRecordExtra

#recordExtra Heron.Check.UnusedImport.ExtraModUseLeaf

#assertImports unused := [Lean.Data.PersistentHashMap]
