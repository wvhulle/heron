module

meta import Heron.Assert
meta import Heron.Check.FunToCdot

#assertCheck funToCdot in
  def f :=
    List.map (fun x => x + 1) [1, 2, 3] becomes
  `(def f :=
      List.map (· + 1) [1, 2, 3])

#assertCheck funToCdot in
  def g :=
    List.filter (fun x => x > 0) [1, 2, 3] becomes
  `(def g :=
      List.filter (· > 0) [1, 2, 3])
