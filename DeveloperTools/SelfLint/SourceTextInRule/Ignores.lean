module

meta import Heron.Assert
meta import DeveloperTools.SelfLint.SourceTextInRule

#assertIgnore sourceTextInRule in
def isSome : Lean.Syntax → Bool
  | `(some $_) => true
  | _ => false

#assertIgnore sourceTextInRule in
example (n : Lean.Name) : Bool := n == `foo

#assertIgnore sourceTextInRule in
example (n : Lean.Name) : Lean.MessageData := m!"unexpected {n}"
