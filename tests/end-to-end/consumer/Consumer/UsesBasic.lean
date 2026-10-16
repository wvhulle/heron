import Consumer.Basic

def incrementOrZero (o : Option Nat) : Nat := match o with
  | some v => increment v
  | _ => 0
