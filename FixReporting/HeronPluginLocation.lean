import Weir.PluginResolution

namespace FixReporting

def pluginSoFileName : String := "libheron_Heron.so"

def findPluginSo : IO (Option String) := do
  if let some p ← IO.getEnv "HERON_PLUGIN_SO" then return some p
  Weir.pluginBesideBinary pluginSoFileName

def queryPluginPath : IO (Option String) :=
  Weir.queryLakeTarget "heron/plugin" IO.eprintln

end FixReporting
