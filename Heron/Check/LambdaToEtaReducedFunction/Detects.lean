module

meta import Heron.Assert
meta import Heron.Check.LambdaToEtaReducedFunction

#assertCheck lambdaToEtaReducedFunction in
def asStrings (xs : List Nat) := xs.map fun n => toString n
becomes `(command| def asStrings (xs : List Nat) := xs.map toString)

#assertCheck lambdaToEtaReducedFunction in
def offsets (k : Nat) (xs : List Nat) := xs.map (fun n => Nat.add k n)
becomes `(command| def offsets (k : Nat) (xs : List Nat) := xs.map (Nat.add k))

#assertCheck lambdaToEtaReducedFunction in
def shifted (k : Nat) (xs : List Nat) := xs.map fun n => Nat.add k n
becomes `(command| def shifted (k : Nat) (xs : List Nat) := xs.map (Nat.add k))
