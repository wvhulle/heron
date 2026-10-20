namespace UserExecutables

def pluginSoFileName : String := "libheron_Heron.so"

def findPluginSo : IO (Option String) := do
  if let some p ← IO.getEnv "HERON_PLUGIN_SO" then return some p
  let cand := (← IO.appDir) / ".." / "lib" / pluginSoFileName
  (some <$> (IO.FS.realPath cand).map (·.toString)) <|> pure none

end UserExecutables
