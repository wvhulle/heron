import Lake
open Lake DSL

require heron from "../.."

package consumer where
  leanOptions := #[⟨`linter.heron, true⟩]
  plugins := #[`@heron/plugin]
  lintDriver := "heron/heron"
  lintDriverArgs := #["lint"]

@[default_target]
lean_lib Consumer
