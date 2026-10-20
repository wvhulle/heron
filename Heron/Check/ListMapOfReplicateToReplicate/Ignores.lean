module

meta import Heron.Assert
meta import Heron.Check.ListMapOfReplicateToReplicate

#assertIgnore listMapOfReplicateToReplicate in
example (n a : Nat) : List Nat := List.replicate n a
