module

meta import Heron.Assert
meta import Heron.Check.FunToCdot

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
