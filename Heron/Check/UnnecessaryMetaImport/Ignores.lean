module

import Heron.Assert
meta import Lean.Data.Lsp.Capabilities

-- Reference `ClientCapabilities` in meta code — `meta` on the Capabilities
-- import is necessary because the module is used inside a meta declaration.
private meta def _usesCapabilitiesInMeta : Option Lean.Lsp.ClientCapabilities := none

#assertImports unused := [] overMeta := []
