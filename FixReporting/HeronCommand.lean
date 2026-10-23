import FixReporting.LintSubcommand
import FixReporting.ScanSubcommand
import FixReporting.RulesSubcommand

open Cli

def printSubcommandHelp (parsed : Parsed) : IO UInt32 := do
  parsed.printHelp
  return 1

unsafe def heronCmd : Cmd := `[Cli|
  heron VIA printSubcommandHelp;
  "Report and apply the fixes of Heron's checks and refactors for Lean 4 projects."

  SUBCOMMANDS:
    lintCmd;
    scanCmd;
    rulesCmd
]

unsafe def main (args : List String) : IO UInt32 :=
  heronCmd.validate args
