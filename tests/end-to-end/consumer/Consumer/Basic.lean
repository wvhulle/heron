def increment (x : Nat) : Nat := Id.run do
  let mut y := x
  return y + 1

example : Nat → Nat → True := by intro a; intro b; exact trivial
