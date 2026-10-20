module

public meta import Heron.Rule
public meta import Lean.PrettyPrinter
meta import Lean.Meta.TryThis

public section

open Lean Elab Command Meta

namespace Heron

/-- Result of running a rule against a single command for testing. -/
structure RunResult where
  /-- How many matches `Rule.detect` produced. Zero means the rule did not fire. -/
  matchCount : Nat
  /-- Text edits derived from those matches' `Rule.replacements`. May be empty
  even when `matchCount > 0` for warning-only rules with no automatic fix. -/
  edits : Array Lsp.TextEdit

/-- Type-erased rule runner: given syntax, produces a detection count and
LSP `TextEdit`s via `Rule.detect` + `Rule.replacements` + `Replacement.toTextEdits`. -/
meta abbrev TestRunner :=
  Syntax → CommandElabM RunResult

/-- Registry of rule runners, keyed by rule name. Used by test macros to
invoke rules directly without going through the linter/diagnostic path. -/
meta initialize testRunnerRegistry : IO.Ref (Std.HashMap Name TestRunner) ←
  IO.mkRef { }

private structure TaggedOutput where
  text : String := ""
  column : Nat := 0
  openTags : List (Nat × Nat) := []
  spans : Std.HashMap Nat (Nat × Nat) := {}

private meta instance : Std.Format.MonadPrettyFormat (StateM TaggedOutput) where
  pushOutput s := modify fun st => { st with text := st.text ++ s, column := st.column + s.length }
  pushNewline indent := modify fun st => { st with text := st.text ++ "\n".pushn ' ' indent, column := indent }
  currColumn := return (← get).column
  startTag tag := modify fun st => { st with openTags := (tag, st.text.utf8ByteSize) :: st.openTags }
  endTags count := modify fun st =>
    { st with
      openTags := st.openTags.drop count
      spans := (st.openTags.take count).foldl (init := st.spans) fun spans (tag, start) =>
        spans.insert tag (start, st.text.utf8ByteSize) }

private structure PieceMarking where
  kept : Array Syntax.Range := #[]
  keptKinds : Array SyntaxNodeKind := #[]
  printedTokens : Array (Nat × String) := #[]
  lastKeptStop : String.Pos.Raw := ⟨0⟩

private meta def originalRange? (stx : Syntax) : Option Syntax.Range :=
  stx.getRange? (canonicalOnly := true)

private meta def copiedFromSource? (source : Syntax) (sourceRange : Syntax.Range) (stx : Syntax) :
    Option Syntax.Range := do
  guard !stx.isOfKind nullKind
  let range ← originalRange? stx
  guard (sourceRange.start ≤ range.start && range.stop ≤ sourceRange.stop)
  let _ ← source.find? fun candidate => originalRange? candidate == some range && candidate.structEq stx
  return range

private meta def markerInfo (marker : Nat) : SourceInfo := .synthetic ⟨marker⟩ ⟨marker⟩

private meta partial def markPieces (copied : Syntax → Option Syntax.Range)
    (excluded : Array (Syntax.Range × SyntaxNodeKind)) (base : Nat) (stx : Syntax) : StateM PieceMarking Syntax := do
  let st ← get
  if let some range := copied stx then
    if !excluded.contains (range, stx.getKind) && st.lastKeptStop ≤ range.start then
      set { st with kept := st.kept.push range, keptKinds := st.keptKinds.push stx.getKind,
                    lastKeptStop := range.stop }
      return stx.setInfo (markerInfo (base + 2 * st.kept.size))
  match stx with
  | .node info kind args => return .node info kind (← args.mapM (markPieces copied excluded base))
  | .missing => return stx
  | token =>
    let text := match token with
      | .atom _ value => value
      | .ident _ rawText _ _ => rawText.toString
      | _ => ""
    if text.isEmpty then return token
    set { st with printedTokens := st.printedTokens.push (st.kept.size, text) }
    return token.setInfo (markerInfo (base + 2 * st.printedTokens.size + 1))

private structure SourceToken where
  range : Syntax.Range
  trailingStop : String.Pos.Raw

private meta partial def sourceTokens : Syntax → Array SourceToken
  | stx@(.atom (.original _ _ trailing _) _) | stx@(.ident (.original _ _ trailing _) _ _ _) =>
    (originalRange? stx).toArray.map ({ range := ·, trailingStop := trailing.stopPos })
  | .node _ _ args => args.flatMap sourceTokens
  | _ => #[]

private meta def widthWithoutSoftLineBreaks : Nat := 100000

private meta partial def markUntilAllKeptTagged (r : Replacement) (copied : Syntax → Option Syntax.Range)
    (base indent column : Nat) (excluded : Array (Syntax.Range × SyntaxNodeKind)) :
    CoreM (PieceMarking × TaggedOutput) := do
  let (marked, marking) := (markPieces copied excluded base r.newSyntax).run {}
  let format ← if marked.isMissing then pure .nil else r.prettyPrint marked
  let ((), output) := (Std.Format.prettyM format widthWithoutSoftLineBreaks indent : StateM TaggedOutput Unit).run { column }
  let untagged := (Array.range marking.kept.size).filterMap fun i =>
    if output.spans.contains (base + 2 * i) then none
    else return (← marking.kept[i]?, ← marking.keptKinds[i]?)
  if untagged.isEmpty then return (marking, output)
  markUntilAllKeptTagged r copied base indent column (excluded ++ untagged)

private meta def withoutSurroundingSpacing (text : String) : Nat × Nat → Nat × Nat
  | (start, stop) =>
    let chars := (String.Pos.Raw.extract text ⟨start⟩ ⟨stop⟩).toList
    let leading := (chars.takeWhile Char.isWhitespace).length
    let trailing := (chars.reverse.takeWhile Char.isWhitespace).length
    if leading + trailing ≥ chars.length then (start, stop) else (start + leading, stop - trailing)

private structure Gap where
  sourceStart : String.Pos.Raw
  sourceStop : String.Pos.Raw
  coveredFrom : String.Pos.Raw
  outputStart : Nat
  outputStop : Nat
  nextKeptStart : String.Pos.Raw
  isLast : Bool
  isFirst : Bool
  allPrintedTagged : Bool
  printedTexts : Array String

private meta def coversWholeGap (gap : Gap) (changed : Array SourceToken) : Bool :=
  match changed.foldl (init := some gap.coveredFrom) fun covered token =>
      covered.bind fun c => if token.range.start ≤ c then some (max c token.trailingStop) else none with
  | some covered => gap.sourceStop ≤ covered
  | none => false

private meta def gapEdit (fileMap : FileMap) (output : String) (sourceTokens : Array SourceToken)
    (printed : Array (Nat × Nat)) (gap : Gap) : Option (Syntax.Range × String) := do
  let slice (a b : Nat) := String.Pos.Raw.extract output ⟨a⟩ ⟨b⟩
  let changedTokens := sourceTokens.filter fun t => gap.sourceStart ≤ t.range.start && t.range.stop ≤ gap.sourceStop
  let changed := changedTokens.map (·.range)
  let added := printed.filter fun (s, e) => gap.outputStart ≤ s && e ≤ gap.outputStop
  let covered := coversWholeGap gap changedTokens
  guard (!covered || changed.map (fun t => String.Pos.Raw.extract fileMap.source t.start t.stop) != gap.printedTexts)
  let (span, text) ← if !gap.allPrintedTagged || !covered then
      pure ((⟨gap.sourceStart, gap.sourceStop⟩ : Syntax.Range), slice gap.outputStart gap.outputStop)
    else match changed[0]?, changed.back?, added[0]?, added.back? with
    | some first, some last, some (addedStart, _), some (_, addedStop) =>
      let breaksLine (a b : String.Pos.Raw) := (fileMap.toPosition a).line < (fileMap.toPosition b).line
      let keepsLeading := gap.sourceStart < first.start && (breaksLine gap.sourceStart first.start ||
        gap.outputStart < addedStart && !(slice gap.outputStart addedStart).contains '\n')
      let keepsTrailing := last.stop < gap.sourceStop && (breaksLine last.stop gap.sourceStop ||
        addedStop < gap.outputStop && !(slice addedStop gap.outputStop).contains '\n')
      pure (⟨if keepsLeading then first.start else gap.sourceStart, if keepsTrailing then last.stop else gap.sourceStop⟩,
        slice (if keepsLeading then addedStart else gap.outputStart) (if keepsTrailing then addedStop else gap.outputStop))
    | none, _, some (addedStart, _), some (_, addedStop) =>
      if gap.isLast then pure (⟨gap.sourceStart, gap.sourceStart⟩, slice gap.outputStart addedStop)
      else pure (⟨gap.sourceStop, gap.sourceStop⟩, slice addedStart gap.outputStop)
    | some first, some last, none, _ =>
      let (lineIndent, lineColumn) := Tactic.TryThis.getIndentAndColumn fileMap ⟨first.start, first.start⟩
      let lastLine := (fileMap.toPosition last.stop).line
      if lineIndent == lineColumn && lastLine < (fileMap.toPosition gap.nextKeptStart).line then
        pure (⟨fileMap.ofPosition ⟨(fileMap.toPosition first.start).line, 0⟩, fileMap.ofPosition ⟨lastLine + 1, 0⟩⟩, "")
      else if gap.isFirst then pure (⟨first.start, gap.sourceStop⟩, "")
      else if gap.isLast || last.stop < gap.sourceStop then pure (⟨gap.sourceStart, last.stop⟩, "")
      else if gap.sourceStart < first.start then pure (⟨first.start, gap.sourceStop⟩, "")
      else pure (⟨gap.sourceStart, gap.sourceStop⟩, slice gap.outputStart gap.outputStop)
    | _, _, _, _ => none
  guard (String.Pos.Raw.extract fileMap.source span.start span.stop != text)
  return (span, text)

meta def Replacement.toTextEdits (r : Replacement) (fileMap : FileMap) : CoreM (Array Lsp.TextEdit) := do
  let some range := r.oldSyntax.getRange? | return #[]
  let (indent, column) := Tactic.TryThis.getIndentAndColumn fileMap range
  let base := fileMap.source.utf8ByteSize + 1
  let (marking, output) ←
    markUntilAllKeptTagged r (copiedFromSource? r.oldSyntax range) base indent column #[]
  let tokenSpan (marker : Nat) := (output.spans[marker]?).map (withoutSurroundingSpacing output.text)
  let keptOutput := (Array.range marking.kept.size).filterMap fun i => tokenSpan (base + 2 * i)
  let printed := (Array.range marking.printedTokens.size).filterMap fun j => tokenSpan (base + 2 * j + 1)
  let gapsWithUntaggedTokens := (Array.range marking.printedTokens.size).filterMap fun j =>
    if output.spans.contains (base + 2 * j + 1) then none else (marking.printedTokens[j]?).map (·.1)
  let tokens := sourceTokens r.oldSyntax
  let afterRange := r.oldSyntax.getTrailingTailPos?.getD range.stop
  let trailingStopAt (stop : String.Pos.Raw) :=
    ((tokens.find? (·.range.stop == stop)).map (·.trailingStop)).getD stop
  let gaps := (Array.range (marking.kept.size + 1)).map fun i =>
    let isLast := i == marking.kept.size
    { sourceStart := if i == 0 then range.start else marking.kept[i - 1]!.stop
      sourceStop := if isLast then range.stop else marking.kept[i]!.start
      coveredFrom := if i == 0 then range.start else trailingStopAt marking.kept[i - 1]!.stop
      outputStart := if i == 0 then 0 else keptOutput[i - 1]!.2
      outputStop := if isLast then output.text.utf8ByteSize else keptOutput[i]!.1
      nextKeptStart := if isLast then afterRange else marking.kept[i]!.start
      isLast, isFirst := i == 0, allPrintedTagged := !gapsWithUntaggedTokens.contains i
      printedTexts := marking.printedTokens.filterMap fun (gap, text) => if gap == i then some text else none : Gap }
  return gaps.filterMap (gapEdit fileMap output.text tokens printed) |>.map
    fun (span, newText) => { range := fileMap.utf8RangeToLspRange span, newText }

/-- Build a type-erased test runner for a `Rule` instance. -/
meta def buildTestRunner [Rule α] : TestRunner := fun stx => do
  let fileMap ← getFileMap
  let results ← Rule.detectAll (α := α) stx
  let edits ← results.flatMapM fun m => do
    let repls ← Rule.replacementsFor m
    repls.flatMapM (liftCoreM <| ·.toTextEdits fileMap)
  return { matchCount := results.size, edits }

end Heron
