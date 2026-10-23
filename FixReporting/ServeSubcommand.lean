import Cli
import Weir
import FixReporting.HeronPluginLocation

open Lean

def isHeronName (json : Json) : Bool :=
  match json.getStr? with
  | .ok name => name.startsWith "heron."
  | .error _ => false

def heronProxyConfig : Weir.ProxyConfig where
  name := "heron"
  repository := "https://github.com/wvhulle/heron"
  pluginTarget := "heron/plugin"
  pluginFileName := FixReporting.pluginSoFileName
  extraServeArgs := #["-Dweak.linter.heron=true"]
  providedCapabilities.codeActionProvider? := some {
    resolveProvider? := true
    codeActionKinds? := some #["quickfix", "refactor"] }
  keepDiagnostic diagnostic := isHeronName (diagnostic.getObjValD "code")
  keepCodeAction action := isHeronName ((action.getObjValD "data").getObjValD "providerName")

def runServe (parsed : Cli.Parsed) : IO UInt32 :=
  Weir.runProxy heronProxyConfig (parsed.variableArgsAs! String)

def serveCmd : Cli.Cmd := `[Cli|
  serve VIA runServe;
  "Run a second Lean language server that shows only Heron's hints and quick fixes, \
   for projects that do not load the Heron plugin themselves."

  ARGS:
    ...leanServerArgs : String; "Arguments passed on to the Lean server; put them after --."
]
