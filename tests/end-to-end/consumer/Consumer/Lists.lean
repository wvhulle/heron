import Consumer.Arithmetic

def doubleAll (xs : List Nat) : List Nat := xs.map double

example : doubleAll [1, 2] = [2, 4] := rfl
