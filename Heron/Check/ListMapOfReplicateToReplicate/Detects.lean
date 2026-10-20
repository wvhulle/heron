module

meta import Heron.Assert
meta import Heron.Check.ListMapOfReplicateToReplicate

#assertCheck listMapOfReplicateToReplicate in
example (f : Nat → Nat) (n a : Nat) : List Nat := List.map f (List.replicate n a)
becomes `(command|
example (f : Nat → Nat) (n a : Nat) : List Nat := List.replicate n (f a))

#assertCheck listMapOfReplicateToReplicate in
example (f : Nat → Nat) (n a : Nat) : List Nat := (List.replicate n a).map f
becomes `(command|
example (f : Nat → Nat) (n a : Nat) : List Nat := List.replicate n (f a))
