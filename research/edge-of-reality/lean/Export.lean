import ER01.Core
import Lean
open ER01 Lean
set_option autoImplicit false

def phaseCode : Phase → Nat
  | .prepared => 0 | .filtered => 1 | .admitted => 2
  | .observed => 3 | .returned => 4 | .rejected => 5

def packedFrame (mode : Mode) (s : Frame) : Json :=
  let visible := s.phase == .observed || s.phase == .returned
  let obs := if visible then toJson ((observation mode s.mass).map fun (label,mass) =>
    toJson [label,mass]) else Json.null
  let post := if visible then match posterior s.mass with
    | none => Json.null
    | some r => toJson [r.numerator,r.denominator]
    else Json.null
  toJson [toJson s.tick,toJson (phaseCode s.phase),toJson s.mass.zero,
    toJson s.mass.one,toJson s.mass.total,obs,post]

def main : IO Unit := do
  let out ← IO.getStdout
  out.putStr "["
  for p in List.range 101 do
    for l in List.range 101 do
      if hp : p ≤ 100 then
        if hl : l ≤ 100 then
          let c : Config := ⟨p,100,l,100,by decide,by decide,hp,hl⟩
          let frames := trace c 4
          let row := toJson [toJson [(weights c).total, commonDenominator c],
            toJson (frames.map (packedFrame .resolved)),
            toJson (frames.map (packedFrame .coarse))]
          if p != 0 || l != 0 then out.putStr ","
          out.putStr row.compress
  out.putStrLn "]"
