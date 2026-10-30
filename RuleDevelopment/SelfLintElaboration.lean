import Lean
import Heron
import FixReporting.FixReportRendering
import FixReporting.BoundedParallelMap

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Frontend Lean.Parser
open Heron (FixRecord RuleEntry collectFixRecords)
open FixReporting (Report boundedParallelMap)

namespace RuleDevelopment

def selfLintOptions : Options := (Elab.async.set ({} : Options) false).setBool `linter.heron true

partial def collectCommandFixes (checks : Array RuleEntry) (collected : Array FixRecord) :
    FrontendM (Array FixRecord) := do
  updateCmdPos
  let commandState ← getCommandState
  let inputContext ← getInputContext
  let parserState ← getParserState
  let scope := commandState.scopes.head!
  let parserModuleContext := { env := commandState.env, options := scope.opts,
                               currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (command, nextParserState, messages) :=
    parseCommand inputContext parserModuleContext parserState commandState.messages
  setParserState nextParserState
  setMessages messages
  let skipsElaboration := command.isOfKind ``Lean.Parser.Command.eval
    || command.isOfKind ``Lean.Parser.Command.evalBang
    || command.isOfKind ``Lean.Parser.Command.initialize
  let collected ← if skipsElaboration then pure collected else do
    elabCommandAtFrontend command
    pure (collected ++ (← runCommandElabM (collectFixRecords false checks command)))
  if isTerminalCommand command then return collected else collectCommandFixes checks collected

structure RuleSourceFile where
  path : String
  source : String
  imports : Array Import

def readRuleSourceFile (path : String) : IO RuleSourceFile := do
  let source ← IO.FS.readFile path
  let header ← Lean.parseImports' source path
  return { path, source, imports := header.imports }

def lintRuleSourceFiles (checks : Array RuleEntry) (concurrency : Nat) (paths : Array String) :
    IO (Array Report) := do
  let ruleSourceFiles ← paths.mapM readRuleSourceFile
  let mut importedModules : Std.HashSet Name := ∅
  for ruleSourceFile in ruleSourceFiles do
    for imported in ruleSourceFile.imports do
      unless imported.module == `Init do importedModules := importedModules.insert imported.module
  let environment ← importModules (importedModules.toArray.map ({ module := · })) selfLintOptions
    (loadExts := true)
  let lintRuleSourceFile : RuleSourceFile → IO Report := fun ruleSourceFile => do
    let inputContext := mkInputContext ruleSourceFile.source ruleSourceFile.path
    let (_, parserState, _) ← parseHeader inputContext
    let frontendState : Frontend.State :=
      { commandState := Command.mkState environment {} selfLintOptions, parserState,
        cmdPos := parserState.pos }
    let (_, (fixes, _)) ← IO.FS.withIsolatedStreams
      (((collectCommandFixes checks #[]).run { inputCtx := inputContext }).run frontendState)
    return { path := some ruleSourceFile.path, label := ruleSourceFile.path,
             fileMap := inputContext.fileMap, fixes }
  boundedParallelMap concurrency ruleSourceFiles lintRuleSourceFile

end RuleDevelopment
