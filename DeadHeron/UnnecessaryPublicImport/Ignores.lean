module

import DeadHeron.Assert
public import Lean.Data.Lsp.Capabilities

-- Reference `ClientCapabilities` in a public declaration — `public` on the
-- Capabilities import is necessary so downstream modules can see the type.
public def usesCapabilitiesPublicly : Option Lean.Lsp.ClientCapabilities := none

#assertImports unused := [] overPublic := []
