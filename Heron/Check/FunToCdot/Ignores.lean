module

meta import Heron.Assert
meta import Heron.Check.FunToCdot

set_option linter.unusedVariables false

-- Ignore: parameter used more than once
#assertIgnore funToCdot in
  def h :=
    List.map (fun x => x + x)
      [1, 2, 3]

-- Ignore: parameter inside parens (· would mis-scope)
#assertIgnore funToCdot in
  def k :=
    List.map (fun x => f (x + 1))
      [1, 2, 3]

-- Ignore: parameter used via a projection/field (`s.field` is not a replaceable bare ident;
-- rewriting only the bare `s` would leave `s.field` dangling)
#assertIgnore funToCdot in
  def kproj (g : Nat → Nat) :=
    List.map (fun s => g s + s.succ)
      [1, 2, 3]

-- Ignore: record update where the parameter is also projected
#assertIgnore funToCdot in
  def kupd :=
    List.map (fun s => { s with fst := s.fst + 1 })
      [({ fst := 0, snd := 0 } : Nat × Nat)]

-- Ignore: multiple parameters
#assertIgnore funToCdot in
  def m :=
    List.map (fun x y => x + y)
      [1, 2, 3]

-- Ignore: body is just the parameter
#assertIgnore funToCdot in
  def n :=
    List.map (fun x => x)
      [1, 2, 3]

-- Ignore: parameter not used
#assertIgnore funToCdot in
  def p :=
    List.map (fun x => 42) [1, 2, 3]
