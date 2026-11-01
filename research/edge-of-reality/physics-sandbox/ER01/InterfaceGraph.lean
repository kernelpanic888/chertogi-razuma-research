import ER01.Instrument
set_option autoImplicit false
namespace ER01.InterfaceGraph

/-- Vertices are states of the system or its classical record registers.
    Interfaces are directed edges labelled by instrument/read operations. -/
inductive State where
  | prepared | success | failure | success0 | success1 | failure0 | failure1
  deriving Repr, BEq, DecidableEq

inductive Interface where
  | filterSuccess | filterFailure | readSuccess0 | readSuccess1 | readFailure0 | readFailure1
  deriving Repr, BEq, DecidableEq

def source : Interface → State
  | .filterSuccess | .filterFailure => .prepared
  | .readSuccess0 | .readSuccess1 => .success
  | .readFailure0 | .readFailure1 => .failure

def target : Interface → State
  | .filterSuccess => .success
  | .filterFailure => .failure
  | .readSuccess0 => .success0
  | .readSuccess1 => .success1
  | .readFailure0 => .failure0
  | .readFailure1 => .failure1

/-- Joint path mass, not a conditional edge probability. For read edges the
    source state's probability must be divided out to obtain that probability. -/
def mass (c : Config) : Interface → Nat
  | .filterSuccess => (weights c).total
  | .filterFailure | .readFailure1 => Instrument.failureMass c
  | .readSuccess0 => (weights c).zero
  | .readSuccess1 => (weights c).one
  | .readFailure0 => 0

def Admissible (c : Config) (e : Interface) : Prop := 0 < mass c e

def rank : State → Nat
  | .prepared => 0
  | .success | .failure => 1
  | _ => 2

/-- The observer reads an outcome flag and, optionally, the system label.
    Changing the readout does not change the graph's underlying states. -/
def record (mode : Mode) : State → Option (Bool × Nat)
  | .success0 => some (true, read mode false)
  | .success1 => some (true, read mode true)
  | .failure0 => some (false, read mode false)
  | .failure1 => some (false, read mode true)
  | _ => none

theorem coarse_records_merge : record .coarse .success0 = record .coarse .success1 := rfl

theorem resolved_records_distinct :
    record .resolved .success0 ≠ record .resolved .success1 := by decide

inductive Path (c : Config) : State → State → Prop where
  | refl (v : State) : Path c v v
  | step (e : Interface) (h : Admissible c e) {v : State}
      (rest : Path c (target e) v) : Path c (source e) v

theorem interface_advances_rank (e : Interface) : rank (source e) < rank (target e) := by
  cases e <;> decide

theorem path_rank_monotone {c : Config} {a b : State} (h : Path c a b) :
    rank a ≤ rank b := by
  induction h with
  | refl => omega
  | step e _ _ ih => exact Nat.le_trans (Nat.le_of_lt (interface_advances_rank e)) ih

theorem no_return_to_prepared (c : Config) (v : State) (h : v ≠ .prepared) :
    ¬ Path c v .prepared := by
  intro path
  have hm := path_rank_monotone path
  cases v <;> simp_all [rank]

theorem failure_zero_is_disabled (c : Config) : ¬ Admissible c .readFailure0 := by
  simp [Admissible, mass]

theorem success_readout_mass_preserved (c : Config) :
    mass c .readSuccess0 + mass c .readSuccess1 = mass c .filterSuccess := rfl

theorem failure_readout_mass_preserved (c : Config) :
    mass c .readFailure0 + mass c .readFailure1 = mass c .filterFailure := by
  simp [mass]

theorem filter_cut_complete (c : Config) :
    mass c .filterSuccess + mass c .filterFailure = commonDenominator c :=
  Instrument.instrument_complete c

theorem zero_success_disables_filter (c : Config) (h : (weights c).total = 0) :
    ¬ Admissible c .filterSuccess := by simp [Admissible, mass, h]

end ER01.InterfaceGraph
