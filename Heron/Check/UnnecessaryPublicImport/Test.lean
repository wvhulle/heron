module

import Heron.Assert
public import Lean.Data.Lsp.Capabilities

-- Reference `Heron.Assert.applyEdits` so `Heron.Assert` is counted as used
-- (the `#assertImports` syntax alone doesn't register a constant reference).
private meta def _usedAssert := @Heron.Assert.applyEdits

-- Reference `ClientCapabilities` privately so `Lean.Data.Lsp.Capabilities`
-- is needed but only in private scope — `public` is unnecessary.
private def _usesCapabilitiesPrivately : Option Lean.Lsp.ClientCapabilities := none

#assertImports unused := [] overPublic := [Lean.Data.Lsp.Capabilities]
