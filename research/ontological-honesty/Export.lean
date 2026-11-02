import Core
open OH01

def region (mask : Nat) : Region := fun w => mask / 2 ^ w.val % 2 == 1

def code : Status → Nat
  | .incompatible => 0
  | .confirmed => 1
  | .refuted => 2
  | .undetermined => 3

def main : IO Unit := do
  let mut rows : Array String := #[]
  for e in [:16] do
    for p in [:16] do
      rows := rows.push s!"[{e},{p},{code (status (region e) (region p))}]"
  IO.println ("[" ++ String.intercalate "," rows.toList ++ "]")
