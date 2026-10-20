import Lean
import Heron
import FixReporting.FixReportRendering

open Lean Heron

namespace FixReporting

private def kindLabel : RuleKind → String
  | .check => "check"
  | .refactor => "refactor"

private def summaryToJson (summary : RuleSummary) : Json :=
  Json.mkObj [
    ("name", toString summary.name),
    ("kind", kindLabel summary.kind),
    ("description", summary.description),
    ("offersFix", summary.offersFix),
    ("sources", toJson (summary.sources.map Source.toLink))]

private def sortedByName (summaries : Array RuleSummary) : Array RuleSummary :=
  summaries.qsort fun a b => toString a.name < toString b.name

private def ruleLines (pal : Palette) (summary : RuleSummary) : List String :=
  let fixNote := if summary.offersFix then "" else pal.dim " (no automatic fix)"
  let sourceLines := summary.sources.toList.map fun source =>
    let link := source.toLink
    s!"    {pal.dim "source:"} {link.title} {pal.url link.url}"
  [s!"  {pal.bold (toString summary.name)}{fixNote}", s!"    {summary.description}"] ++ sourceLines

private def groupLines (pal : Palette) (heading : String) (summaries : Array RuleSummary) :
    List String :=
  pal.blue heading :: "" :: (sortedByName summaries).toList.flatMap fun summary =>
    ruleLines pal summary ++ [""]

def renderRuleCatalog (pal : Palette) (summaries : Array RuleSummary) : String :=
  let checks := summaries.filter (·.kind == .check)
  let refactors := summaries.filter (·.kind == .refactor)
  let checksHeading := s!"Checks ({checks.size}): run on every command once `linter.heron` is on; \
    turn one off with `set_option linter.<rule> false`"
  let refactorsHeading := s!"Refactors ({refactors.size}): offered in the editor's code-action menu, \
    never flag anything"
  String.intercalate "\n" (groupLines pal checksHeading checks ++ groupLines pal refactorsHeading refactors)

def emitRuleCatalog (summaries : Array RuleSummary) (pal : Palette) (json : Bool) : IO Unit := do
  if json then
    IO.println (toJson (summaries.map summaryToJson)).compress
  else
    IO.println (renderRuleCatalog pal summaries)

unsafe def loadRuleInitializers (projectSearchPath : SearchPath := ∅) : IO Unit := do
  initSearchPath (← findSysroot) projectSearchPath
  enableInitializersExecution

end FixReporting

open Cli FixReporting

unsafe def runRules (parsed : Parsed) : IO UInt32 := do
  loadRuleInitializers
  let json := parsed.hasFlag "json"
  let pal : Palette := { on := ← decideColor (requestedColor parsed) json }
  emitRuleCatalog (← Heron.ruleCatalog.get) pal json
  return 0

unsafe def rulesCmd : Cmd := `[Cli|
  rules VIA runRules;
  "List every check and refactor with its description and sources."

  FLAGS:
    json;       "Print the list as JSON."
    color;      "Color the output even when stdout is not a terminal."
    "no-color"; "Never color the output."
]
