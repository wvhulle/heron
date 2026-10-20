namespace FixReporting

def pluginSoFileName : String := "libheron_Heron.so"

def findPluginSo : IO (Option String) := do
  if let some p ← IO.getEnv "HERON_PLUGIN_SO" then return some p
  let cand := (← IO.appDir) / ".." / "lib" / pluginSoFileName
  (some <$> (IO.FS.realPath cand).map (·.toString)) <|> pure none

def queryPluginPath (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) : IO (Option String) := do
  let out ← IO.Process.output { cmd := "lake", args := #["query", "heron/plugin"], cwd, env }
  IO.eprint out.stderr
  let path := out.stdout.trimAscii.toString
  return if out.exitCode == 0 && !path.isEmpty then some path else none

end FixReporting
