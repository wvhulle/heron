import Heron.Assert
import Heron.Check.BoolMatchToIf

-- Reference a constant defined in `Heron.Assert` so the analysis
-- counts it as "used". `#assertImports` below is a syntax extension,
-- not a constant reference, so it would not register on its own.
private def _used := @Heron.Assert.applyEdits

-- #assertImports unused := [Heron.Check.BoolMatchToIf]
#assertImports unused := [Heron.Check.BoolMatchToIf]
