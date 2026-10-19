module

public import Lean.Data.Json

public section

open Lean

namespace Heron

inductive Source where
  | functionalProgrammingInLean (topic : String) (path : String)
  | metaprogrammingInLean (topic : String) (path : String)
  | leanStdStyleGuide (topic : String) (anchor : String)
  | mathlibStyleGuide (topic : String) (anchor : String)
  | hlint (hint : String)
  | clippy (lint : String)
  deriving Inhabited, BEq

structure SourceLink where
  title : String
  url : String
  deriving Inhabited, BEq, ToJson, FromJson

def Source.toLink : Source → SourceLink
  | .functionalProgrammingInLean topic path =>
    { title := s!"Functional Programming in Lean: {topic}"
      url := s!"https://lean-lang.org/functional_programming_in_lean/{path}" }
  | .metaprogrammingInLean topic path =>
    { title := s!"Metaprogramming in Lean 4: {topic}"
      url := s!"https://leanprover-community.github.io/lean4-metaprogramming-book/main/{path}" }
  | .leanStdStyleGuide topic anchor =>
    { title := s!"Lean standard library style guide: {topic}"
      url := s!"https://github.com/leanprover/lean4/blob/master/doc/std/style.md#{anchor}" }
  | .mathlibStyleGuide topic anchor =>
    { title := s!"Mathlib style guide: {topic}"
      url := s!"https://leanprover-community.github.io/contribute/style.html#{anchor}" }
  | .hlint hint =>
    { title := s!"hlint: {hint}"
      url := "https://github.com/ndmitchell/hlint/blob/master/data/hlint.yaml" }
  | .clippy lint =>
    { title := s!"Clippy: {lint}"
      url := s!"https://rust-lang.github.io/rust-clippy/master/index.html#{lint}" }

end Heron
