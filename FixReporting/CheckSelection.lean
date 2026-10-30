import Lean
import Heron

open Lean Heron

namespace FixReporting

def selectChecks (registry : Array RuleEntry) (requested : Array Name) :
    Except String (Array RuleEntry) :=
  if requested.isEmpty then .ok registry
  else requested.mapM fun name =>
    match registry.find? (·.name == name) with
    | some entry => .ok entry
    | none => .error s!"unknown check `{name}`; known checks: {(registry.map (·.name)).toList}"

end FixReporting
