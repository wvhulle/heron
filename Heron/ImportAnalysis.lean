/-
Import analysis infrastructure for detecting unused and over-qualified imports.

The core algorithm is adapted from Lake's Shake (`Lake/CLI/Shake.lean`)
by Mario Carneiro and Sebastian Ullrich, ported to work within `CommandElabM`
for single-file in-editor analysis.

Source: https://github.com/leanprover/lean4/blob/master/src/lake/Lake/CLI/Shake.lean
-/
import Lean.Elab.Command
import Lean.Parser.Module
import Lean.ExtraModUses
import Lean.ResolveName

open Lean Elab Command Parser

namespace Heron.ImportAnalysis

/-! ## NeedsKind and Needs — adapted from Lake.Shake -/

/-- The kind of a module dependency: public/private × meta/non-meta. -/
structure NeedsKind where
  isExported : Bool
  isMeta : Bool
  deriving Inhabited, BEq, Repr, Hashable

namespace NeedsKind

@[match_pattern] abbrev priv : NeedsKind := { isExported := false, isMeta := false }
@[match_pattern] abbrev pub : NeedsKind := { isExported := true, isMeta := false }
@[match_pattern] abbrev metaPriv : NeedsKind := { isExported := false, isMeta := true }
@[match_pattern] abbrev metaPub : NeedsKind := { isExported := true, isMeta := true }

def all : Array NeedsKind := #[pub, priv, metaPub, metaPriv]

def ofImport : Lean.Import → NeedsKind
  | { isExported := true, isMeta := true, .. } => .metaPub
  | { isExported := true, isMeta := false, .. } => .pub
  | { isExported := false, isMeta := true, .. } => .metaPriv
  | { isExported := false, isMeta := false, .. } => .priv

end NeedsKind

/-- A map `NeedsKind → Set ModuleIdx`. Uses `Std.HashSet` instead of Shake's `Bitset`. -/
structure Needs where
  pub : Std.HashSet Nat := {}
  priv : Std.HashSet Nat := {}
  metaPub : Std.HashSet Nat := {}
  metaPriv : Std.HashSet Nat := {}
  deriving Inhabited

namespace Needs

def get (needs : Needs) (k : NeedsKind) : Std.HashSet Nat :=
  match k with
  | .pub => needs.pub
  | .priv => needs.priv
  | .metaPub => needs.metaPub
  | .metaPriv => needs.metaPriv

def has (needs : Needs) (k : NeedsKind) (i : ModuleIdx) : Bool :=
  needs.get k |>.contains i

def set (needs : Needs) (k : NeedsKind) (s : Std.HashSet Nat) : Needs :=
  match k with
  | .pub => { needs with pub := s }
  | .priv => { needs with priv := s }
  | .metaPub => { needs with metaPub := s }
  | .metaPriv => { needs with metaPriv := s }

def modify (needs : Needs) (k : NeedsKind) (f : Std.HashSet Nat → Std.HashSet Nat) : Needs :=
  needs.set k (f (needs.get k))

def unionSet (needs : Needs) (k : NeedsKind) (s : Std.HashSet Nat) : Needs :=
  needs.modify k fun old => s.fold (init := old) fun acc v => acc.insert v

def unionSingleton (needs : Needs) (k : NeedsKind) (i : Nat) : Needs :=
  needs.modify k (·.insert i)

/-- Remove elements in `s` from the given kind. -/
def sub (needs : Needs) (k : NeedsKind) (s : Std.HashSet Nat) : Needs :=
  needs.modify k fun old => old.filter fun v => !s.contains v

end Needs

instance : Union Needs where
  union a b :=
    { pub := b.pub.fold (init := a.pub) fun acc v => acc.insert v
      priv := b.priv.fold (init := a.priv) fun acc v => acc.insert v
      metaPub := b.metaPub.fold (init := a.metaPub) fun acc v => acc.insert v
      metaPriv := b.metaPriv.fold (init := a.metaPriv) fun acc v => acc.insert v }

/-- Check if any kind has the given module index. -/
def Needs.hasAny (needs : Needs) (i : ModuleIdx) : Bool :=
  needs.pub.contains i || needs.priv.contains i ||
  needs.metaPub.contains i || needs.metaPriv.contains i

/-- Check if the module is needed as exported (public). -/
def Needs.hasExported (needs : Needs) (i : ModuleIdx) : Bool :=
  needs.pub.contains i || needs.metaPub.contains i

/-- Check if the module is needed as meta. -/
def Needs.hasMeta (needs : Needs) (i : ModuleIdx) : Bool :=
  needs.metaPub.contains i || needs.metaPriv.contains i

/-! ## Transitive import computation — adapted from Shake.addTransitiveImps -/

/-- Compute transitive reachability through an import, preserving visibility rules.
Adapted from `Lake.Shake.addTransitiveImps`. -/
def addTransitiveImps (transImps : Needs) (imp : Import) (j : Nat) (impTransImps : Needs) : Needs := Id.run do
  let mut transImps := transImps
  -- public non-meta import: transitive public reach
  if imp.isExported && !imp.isMeta then
    transImps := transImps.unionSingleton .pub j |>.unionSet .pub (impTransImps.get .pub)
  -- private non-meta import
  if !imp.isExported && !imp.isMeta then
    transImps := transImps.unionSingleton .priv j |>.unionSet .priv (impTransImps.get .pub)
    if imp.importAll then
      transImps := transImps.unionSet .priv
        (impTransImps.get .pub |>.fold (init := impTransImps.get .priv) fun acc v => acc.insert v)
  -- public meta propagation
  if imp.isExported then
    transImps := transImps.unionSet .metaPub (impTransImps.get .metaPub)
    if imp.isMeta then
      transImps := transImps.unionSingleton .metaPub j
        |>.unionSet .metaPub (impTransImps.get .pub |>.fold (init := impTransImps.get .metaPub) fun acc v => acc.insert v)
  -- private meta propagation
  if !imp.isExported then
    if imp.isMeta then
      transImps := transImps.unionSingleton .metaPriv j
        |>.unionSet .metaPriv (impTransImps.get .pub |>.fold (init := impTransImps.get .metaPub) fun acc v => acc.insert v)
    if imp.importAll then
      transImps := transImps.unionSet .metaPriv
        (impTransImps.get .metaPub |>.fold (init := impTransImps.get .metaPriv) fun acc v => acc.insert v)
    else
      transImps := transImps.unionSet .metaPriv (impTransImps.get .metaPub)
  transImps

/-- Build the transitive dependency array for all modules.
Adapted from `Lake.Shake.initStateFromEnv`. -/
def buildTransDeps (env : Environment) : Array Needs := Id.run do
  let mut transDeps : Array Needs := #[]
  for _ in [:env.header.moduleData.size] do
    transDeps := transDeps.push default
  for i in [:env.header.moduleData.size] do
    let mod := env.header.moduleData[i]!
    let mut transImps : Needs := default
    for imp in mod.imports do
      if let some j := env.getModuleIdx? imp.module then
        transImps := addTransitiveImps transImps imp j (transDeps[j]?.getD default)
    transDeps := transDeps.set! i transImps
  transDeps

/-! ## Needs computation — adapted from Shake.calcNeeds -/

/-- Determine if a declaration is meta. Adapted from `Lake.Shake.isDeclMeta'`. -/
private def isDeclMeta' (env : Environment) (declName : Name) : Bool :=
  let inferFor :=
    if declName.isStr && (declName.getString!.startsWith "match_" || declName.getString! == "_unsafe_rec")
    then declName.getPrefix else declName
  isMarkedMeta env inferFor || isDeclMeta env inferFor

/-- Compute the needs of the current file from file-local constants and extra mod uses.
Adapted from `Lake.Shake.calcNeeds` but operating on stage-2 (file-local) constants. -/
def computeNeeds (env : Environment) (_transDeps : Array Needs) : Needs := Id.run do
  let reservedNames : Std.HashSet Name := Id.run do
    let mut m : Std.HashSet Name := {}
    for (c, _) in env.constants do
      if isReservedName env c then
        m := m.insert c
    return m
  let indirectModUses := indirectModUseExt.getState env
  let mut needs : Needs := default
  -- Iterate file-local constants (stage 2 of the SMap)
  let kenv := env.toKernelEnv
  needs := kenv.constants.foldStage2 (fun needs _name ci =>
    let pubCI? := guard (!isPrivateName ci.name) *> (env.setExporting true).find? ci.name
    let k : NeedsKind := { isExported := pubCI?.isSome, isMeta := isDeclMeta' env ci.name }
    let needs := visitExpr env reservedNames indirectModUses k ci.type needs
    match ci.value? (allowOpaque := true) with
    | some e =>
      let k := if k.isMeta then k else
        if pubCI?.any (·.hasValue (allowOpaque := true)) then .pub else .priv
      visitExpr env reservedNames indirectModUses k e needs
    | none => needs) needs
  -- TODO: include ExtraModUses stage-2 entries once we can access
  -- Lean.extraModUses from non-builtin code. These handle implicit deps
  -- from syntax extensions, attributes, etc.
  return needs
where
  visitExpr (env : Environment) (reservedNames : Std.HashSet Name)
      (indirectModUses : Std.HashMap Name (Array ModuleIdx))
      (k : NeedsKind) (e : Expr) (deps : Needs) : Needs :=
    Expr.foldConsts e deps fun c deps => Id.run do
      let mut deps := deps
      -- Skip reserved names
      if reservedNames.contains c then return deps
      -- Normalize _simp_ constants
      let c := if c.isStr && c.getString!.startsWith "_simp_" then c.getPrefix else c
      if let some j := env.getModuleIdxFor? c then
        let k := { k with isMeta := k.isMeta && !isDeclMeta' env c }
        deps := deps.unionSingleton k j
        -- Include indirect mod uses
        for indMod in indirectModUses[c]?.getD #[] do
          deps := deps.unionSingleton k indMod
      return deps

/-! ## Header parsing -/

/-- Decode a header syntax into its components.
Adapted from `Lake.Shake.decodeHeader`. -/
def decodeHeader : TSyntax ``Parser.Module.header →
    Option (TSyntax `module) × Option (TSyntax `prelude) × TSyntaxArray ``Module.import
  | `(Module.header| $[module%$moduleTk?]? $[prelude%$preludeTk?]? $imports*) =>
    (moduleTk?.map .mk, preludeTk?.map .mk, imports)
  | _ => (none, none, #[])

/-- Decode an import syntax into an `Import`.
Adapted from `Lake.Shake.decodeImport`. -/
def decodeImport : TSyntax ``Module.import → Import
  | `(Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id) =>
    { module := id.getId, isExported := pubTk?.isSome, isMeta := metaTk?.isSome, importAll := allTk?.isSome }
  | _ => { module := .anonymous }

/-- Parse the file header to get import syntax nodes with position information. -/
def parseImportSyntax (fileMap : FileMap) (fileName : String) :
    IO (TSyntax ``Parser.Module.header) := do
  let inputCtx := Parser.mkInputContext fileMap.source fileName
  let (header, _, _) ← Parser.parseHeader inputCtx
  return header

/-! ## ImportAnalysis result -/

/-- Result of analyzing one direct import. -/
structure ImportAnalysis where
  /-- The decoded import. -/
  imp : Import
  /-- The import syntax node (for diagnostic position via `emphasize`). -/
  importStx : Syntax
  /-- Whether this import is needed at all. -/
  isNeeded : Bool
  /-- Whether this import needs to be `public`. -/
  needsExported : Bool
  /-- Whether this import needs to be `meta`. -/
  needsMeta : Bool

/-! ## Last command detection -/

/-- Check if the current command is the last one in the file.
Returns true when the remaining file content after this command is only whitespace. -/
def isLastCommand (stx : Syntax) : CommandElabM Bool := do
  -- The `eoi` (end-of-input) marker is not a real command
  if stx.getKind == ``Lean.Parser.Command.eoi then return false
  let fileMap ← getFileMap
  let stxEnd := stx.getTailPos?.getD ⟨0⟩
  let remaining := String.Pos.Raw.extract fileMap.source stxEnd fileMap.source.rawEndPos
  return remaining.trimAscii.isEmpty

/-! ## Main analysis entry point -/

/-- Cached analysis results. Keyed by `(mainModule, stxPos)` to:
- Share results across the three checks running on the same command (same key)
- Avoid duplicate emission if the module is elaborated more than once (same key → cache hit) -/
initialize importAnalysisCache :
    IO.Ref (Option (Name × String.Pos.Raw × Array ImportAnalysis)) ← IO.mkRef none

/-- Analyze all direct imports of the current file.
Returns an `ImportAnalysis` for each explicit import, determining if it's needed
and what visibility level is minimally required.

This is the main entry point called by all three import checks. The result is
cached so only the first call per file does actual work. -/
def analyzeImports (stx : Syntax) : CommandElabM (Array ImportAnalysis) := do
  unless (← isLastCommand stx) do return #[]
  let env ← getEnv
  let mainMod := env.mainModule
  let stxPos := stx.getPos?.getD ⟨0⟩
  -- Cache hit: same file and same command position already analyzed
  if let some (mod, pos, results) := (← importAnalysisCache.get) then
    if mod == mainMod && pos == stxPos then return results
  let results ← computeAnalysis env
  importAnalysisCache.set (some (mainMod, stxPos, results))
  return results
where
  computeAnalysis (env : Environment) : CommandElabM (Array ImportAnalysis) := do
    let fileMap ← getFileMap
    let fileName ← getFileName
    let headerStx ← parseImportSyntax fileMap fileName
    let (_, prelude?, importsSyntax) := decodeHeader headerStx
    -- Build transitive deps for all imported modules
    let transDeps := buildTransDeps env
    -- Compute what the current file needs
    let needs := computeNeeds env transDeps
    -- Build transitive reachability for the current file's direct imports
    let directImports := env.header.imports
    let mut curTransDeps : Needs := default
    for imp in directImports do
      if let some j := env.getModuleIdx? imp.module then
        curTransDeps := addTransitiveImps curTransDeps imp j (transDeps[j]?.getD default)
    -- Add Init if no prelude
    let mut deps := needs
    if prelude?.isNone then
      if let some initIdx := env.getModuleIdx? `Init then
        deps := deps.unionSingleton .pub initIdx
    -- Transitive reduction: remove modules that are implied by other needed imports
    for j in [:env.header.moduleData.size] do
      let jTransDeps := transDeps[j]?.getD default
      for k in NeedsKind.all do
        if deps.has k j then
          let implied := addTransitiveImps default
            { module := .anonymous, isExported := k.isExported, isMeta := k.isMeta } j jTransDeps
          let singleton : Std.HashSet Nat := ({} : Std.HashSet Nat).insert j
          for k' in NeedsKind.all do
            let reduced := (implied.sub k' singleton).get k'
            deps := deps.sub k' reduced
    -- Determine which direct imports are unused
    let mut results : Array ImportAnalysis := #[]
    -- Match syntax to imports (skip implicit Init)
    let explicitImports := importsSyntax.map fun stx => (decodeImport stx, stx.raw)
    for (imp, impStx) in explicitImports do
      if let some j := env.getModuleIdx? imp.module then
        let k := NeedsKind.ofImport imp
        let isNeeded := deps.has k j || imp.importAll
        -- Check if a private version would cover it (unnecessary public)
        let needsExported := deps.has .pub j || deps.has .metaPub j
        -- Check if a non-meta version would cover it (unnecessary meta)
        let needsMeta := deps.has .metaPub j || deps.has .metaPriv j
        -- Also check if implied by other imports' transitive deps
        let isImplied := curTransDeps.has k j && !isNeeded
        results := results.push {
          imp, importStx := impStx
          isNeeded := isNeeded && !isImplied
          needsExported, needsMeta
        }
      else
        -- Module not found — don't flag it (might be a build error)
        results := results.push {
          imp, importStx := impStx
          isNeeded := true, needsExported := imp.isExported, needsMeta := imp.isMeta
        }
    return results

end Heron.ImportAnalysis
