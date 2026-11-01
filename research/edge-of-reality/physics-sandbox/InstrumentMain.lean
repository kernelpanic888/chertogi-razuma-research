import ER01.InterfaceGraph
import Lean
open ER01 ER01.Instrument Lean
set_option autoImplicit false

def stateName : InterfaceGraph.State → String
  | .prepared => "prepared"
  | .success => "success"
  | .failure => "failure"
  | .success0 => "success0"
  | .success1 => "success1"
  | .failure0 => "failure0"
  | .failure1 => "failure1"

def interfaceName : InterfaceGraph.Interface → String
  | .filterSuccess => "filterSuccess"
  | .filterFailure => "filterFailure"
  | .readSuccess0 => "readSuccess0"
  | .readSuccess1 => "readSuccess1"
  | .readFailure0 => "readFailure0"
  | .readFailure1 => "readFailure1"

def graphJson (c : Config) : Json :=
  let edges : List InterfaceGraph.Interface := [.filterSuccess,.filterFailure,
    .readSuccess0,.readSuccess1,.readFailure0,.readFailure1]
  toJson (edges.map fun e => Json.mkObj [
    ("id",toJson (interfaceName e)),
    ("source",toJson (stateName (InterfaceGraph.source e))),
    ("target",toJson (stateName (InterfaceGraph.target e))),
    ("mass",toJson (InterfaceGraph.mass c e)),
    ("admissible",toJson (decide (0 < InterfaceGraph.mass c e))),
    ("resolvedRecord",toJson (InterfaceGraph.record .resolved (InterfaceGraph.target e))),
    ("coarseRecord",toJson (InterfaceGraph.record .coarse (InterfaceGraph.target e)))])

def predict (c : Config) : Json :=
  Json.mkObj [
    ("schema", toJson "ER01-INSTRUMENT/1"),
    ("p", toJson c.p), ("q", toJson c.q),
    ("l", toJson c.l), ("d", toJson c.d),
    ("denominator", toJson (commonDenominator c)),
    ("masses", toJson (outcomeMasses c)),
    ("successMass", toJson (weights c).total),
    ("failureMass", toJson (failureMass c)),
    ("interfaces",graphJson c),
    ("posteriorZero", match posterior (weights c) with
      | none => Json.null
      | some r => Json.mkObj [("numerator",toJson r.numerator),
                             ("denominator",toJson r.denominator)])]

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let err ← IO.getStderr
  match args with
  | ["--grid"] =>
    for p in List.range 101 do
      for l in List.range 101 do
        if hp : p ≤ 100 then
          if hl : l ≤ 100 then
            let c : Config := ⟨p,100,l,100,by decide,by decide,hp,hl⟩
            out.putStrLn (predict c).compress
    return 0
  | [ps, ls] =>
    match ps.toNat?, ls.toNat? with
    | some p, some l =>
      if hp : p ≤ 100 then
        if hl : l ≤ 100 then
          let c : Config := ⟨p,100,l,100,by decide,by decide,hp,hl⟩
          out.putStrLn (predict c).compress
          return 0
        else err.putStrLn "lambda must be 0..100"
      else err.putStrLn "p must be 0..100"
    | _, _ => err.putStrLn "Expected integer percentages"
  | _ => err.putStrLn "Usage: instrument pPercent lambdaPercent"
  return 2
