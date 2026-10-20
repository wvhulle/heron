module

meta import Heron.Assert
meta import Heron.Check.ListFlattenOfMapToFlatMap

#assertIgnore listFlattenOfMapToFlatMap in
example (xss : List (List Nat)) : List Nat := xss.flatten
