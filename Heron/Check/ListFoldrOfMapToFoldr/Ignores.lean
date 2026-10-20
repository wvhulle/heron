module

meta import Heron.Assert
meta import Heron.Check.ListFoldrOfMapToFoldr

#assertIgnore listFoldrOfMapToFoldr in
example (g : Nat → Nat → Nat) (xs : List Nat) : Nat := xs.foldr g 0
