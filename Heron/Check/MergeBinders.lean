module

public meta import Heron.Check

open Lean Elab Command Parser Heron

/-- Create a `Syntax` spanning two syntax nodes. -/
private meta def mkSpan (stx1 stx2 : Syntax) : Option Syntax := do
  let r1 ← stx1.getRange?
  let r2 ← stx2.getRange?
  return Syntax.ofRange ⟨r1.start, r2.stop⟩

private structure MergeBindersMatch where
  secondBinder : Syntax
  fullRange : Syntax
  binder1 : Syntax
  binder2 : Syntax

/-- Get the type text of an explicitBinder, if it has a type annotation. -/
private meta def binderTypeText? (binder : Syntax) : Option String :=
  let typeSpec := binder[2]!
  if typeSpec.getNumArgs >= 2 then some (reprintTrimmed typeSpec[1]!)
  else none

/-- Check if an explicitBinder has a default value. -/
private meta def hasDefault (binder : Syntax) : Bool :=
  binder[3]!.getNumArgs > 0

/-- Get the variable name texts from an explicitBinder. -/
private meta def binderNames (binder : Syntax) : Array String :=
  let names := binder[1]!  -- null-node of idents
  names.getArgs.map reprintTrimmed

/-- Find pairs of consecutive explicit binders in a signature's binder list. -/
private meta def findMergeableInBinders (binders : Array Syntax) : Array MergeBindersMatch :=
  if binders.size < 2 then #[]
  else
    (List.range (binders.size - 1)).foldl (init := #[]) fun acc i =>
      let b1 := binders[i]!
      let b2 := binders[i + 1]!
      if b1.getKind != ``Term.explicitBinder then acc
      else if b2.getKind != ``Term.explicitBinder then acc
      else if hasDefault b1 || hasDefault b2 then acc
      else
        match binderTypeText? b1, binderTypeText? b2 with
        | some t1, some t2 =>
          if t1 == t2 then
            match mkSpan b1 b2 with
            | some fullRange => acc.push { secondBinder := b2, fullRange, binder1 := b1, binder2 := b2 }
            | none => acc
          else acc
        | _, _ => acc

private meta instance : Check MergeBindersMatch where
  name := `mergeBinders
  kinds := #[``Command.optDeclSig, ``Command.declSig]
  severity := .information
  category := .style
  detect := fun stx => pure <|
    let binderSeq := stx[0]!
    findMergeableInBinders binderSeq.getArgs
  message := fun _ => m!"Merge binders with the same type"
  emphasize := fun m => m.secondBinder
  reference := some { topic := "Shared binders", url := "https://leanprover.github.io/functional_programming_in_lean/monads/conveniences.html" }
  explanation := fun _ => m!"Consecutive explicit binders with the same type can be merged into a single binder group."
  replacements := fun m => do
    -- Merge the ident lists from both binders, keep the type from the first
    let names1 := m.binder1[1]!.getArgs
    let names2 := m.binder2[1]!.getArgs
    let allNames : TSyntaxArray `ident := (names1 ++ names2).map (⟨·⟩)
    let ty : TSyntax `term := ⟨m.binder1[2]![1]!⟩
    let repl ← `(bracketedBinder| ($allNames* : $ty))
    return #[{
      emphasizedSyntax := m.secondBinder
      oldSyntax := m.fullRange
      newSyntax := repl
      inlineViolationLabel := m!"shared type"
      category := `bracketedBinder
    }]

meta initialize Check.register (α := MergeBindersMatch)
