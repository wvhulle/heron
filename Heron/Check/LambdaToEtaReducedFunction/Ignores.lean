module

meta import Heron.Assert
meta import Heron.Check.LambdaToEtaReducedFunction

#assertIgnore lambdaToEtaReducedFunction in
def usedTwice (xs : List Nat) := xs.map fun n => Nat.add n n

#assertIgnore lambdaToEtaReducedFunction in
def nestedUse (xs : List Nat) := xs.map fun n => Nat.succ (Nat.succ n)

#assertIgnore lambdaToEtaReducedFunction in
def notLast (xs : List Nat) := xs.map fun n => Nat.sub n 1

#assertIgnore lambdaToEtaReducedFunction in
def identity (xs : List Nat) := xs.map fun n => n
