module

import Heron.Assert
meta import Lean.Data.Lsp.Capabilities

-- Reference `Heron.Assert.applyEdits` so `Heron.Assert` is counted as used.
private meta def _usedAssert := @Heron.Assert.applyEdits

-- Reference `ClientCapabilities` in non-meta code — `meta` on the Capabilities
-- import is unnecessary since the module is only used for type signatures.
private def _usesCapabilitiesNonMeta : Option Lean.Lsp.ClientCapabilities := none

#assertImports unused := [] overMeta := [Lean.Data.Lsp.Capabilities]
