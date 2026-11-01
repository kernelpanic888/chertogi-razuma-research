import ER01.Core
import Lean
open ER01 Lean
set_option autoImplicit false

def phaseName : Phase → String
  | .prepared => "prepared"
  | .filtered => "filtered"
  | .admitted => "admitted"
  | .observed => "observed"
  | .returned => "returned"
  | .rejected => "rejected"

def ratioJson (n d : Nat) : Json :=
  Json.mkObj [("numerator", toJson n), ("denominator", toJson d)]

def massJson (m : Mass) : Json :=
  Json.mkObj [("zero", toJson m.zero), ("one", toJson m.one), ("total", toJson m.total)]

def frameJson (mode : Mode) (s : Frame) : Json :=
  let visible := s.phase == .observed || s.phase == .returned
  let reading := if visible then
    toJson ((observation mode s.mass).map fun (label, mass) =>
      Json.mkObj [("label", toJson label), ("mass", toJson mass)]) else Json.null
  let conditional := if visible then
    match posterior s.mass with
    | none => Json.null
    | some r => ratioJson r.numerator r.denominator
    else Json.null
  Json.mkObj [("tick", toJson s.tick), ("phase", toJson (phaseName s.phase)),
    ("mass", massJson s.mass), ("readout", reading), ("conditionalBranchZero", conditional)]

def simulate (c : Config) (n : Nat) (mode : Mode) : Json :=
  Json.mkObj [("schema", toJson "ER01/1"), ("model", toJson "diagonal-qubit-filter"),
    ("input", Json.mkObj [("p", toJson c.p), ("q", toJson c.q),
      ("lambdaNumerator", toJson c.l), ("lambdaDenominator", toJson c.d)]),
    ("mode", toJson (if mode == .coarse then "coarse" else "resolved")),
    ("successWeight", ratioJson (weights c).total (commonDenominator c)),
    ("trace", toJson ((trace c n).map (frameJson mode)))]

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match args with
  | [ps, qs, ls, ds, ns, ms] =>
    match ps.toNat?, qs.toNat?, ls.toNat?, ds.toNat?, ns.toNat? with
    | some p, some q, some l, some d, some n =>
      if hq : 0 < q then
        if hd : 0 < d then
          if hp : p ≤ q then
            if hl : l ≤ d then
              if n ≤ 1000 && q ≤ 10000 && d ≤ 10000 &&
                  (ms == "coarse" || ms == "resolved") then
                let c : Config := ⟨p, q, l, d, hq, hd, hp, hl⟩
                let mode := if ms == "coarse" then Mode.coarse else Mode.resolved
                out.putStrLn (simulate c n mode).compress
                return 0
              else
                err.putStrLn "Invalid mode or resource limit (steps<=1000, q,d<=10000)."
            else err.putStrLn "lambda numerator exceeds denominator."
          else err.putStrLn "p exceeds q."
        else err.putStrLn "lambda denominator must be positive."
      else err.putStrLn "q must be positive."
      return 2
    | _, _, _, _, _ =>
      err.putStrLn "All numeric inputs must be natural numbers."
      return 2
  | _ =>
    err.putStrLn "Usage: er01 p q lambdaNumerator lambdaDenominator steps coarse|resolved"
    return 2
