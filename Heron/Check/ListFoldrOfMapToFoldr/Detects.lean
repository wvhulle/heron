module

meta import Heron.Assert
meta import Heron.Check.ListFoldrOfMapToFoldr

#assertCheck listFoldrOfMapToFoldr in
example (f : Nat → Nat) (g : Nat → Nat → Nat) (xs : List Nat) : Nat := List.foldr g 0 (List.map f xs)
becomes `(command|
example (f : Nat → Nat) (g : Nat → Nat → Nat) (xs : List Nat) : Nat := List.foldr (fun x y => g (f x) y) 0 xs)

#assertCheck listFoldrOfMapToFoldr in
example (f : Nat → Nat) (x : Nat → Nat → Nat) (y : Nat) (xs : List Nat) : Nat := (xs.map f).foldr x y
becomes `(command|
example (f : Nat → Nat) (x : Nat → Nat → Nat) (y : Nat) (xs : List Nat) : Nat := List.foldr (fun x_1 y_1 => x (f x_1) y_1) y xs)
