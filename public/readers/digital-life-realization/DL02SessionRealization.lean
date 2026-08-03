import DigitalLifePassport

namespace DigitalLifePassport
namespace DL02

inductive Phase where
  | protocolFrozen
  | leanReplayed
  | readerChecked
  | securityChecked
  deriving DecidableEq, Repr

def nextPhase : Phase -> Phase
  | .protocolFrozen => .leanReplayed
  | .leanReplayed => .readerChecked
  | .readerChecked => .securityChecked
  | .securityChecked => .protocolFrozen

theorem nextPhase_ne_self (s : Phase) : Not (nextPhase s = s) := by
  cases s <;> decide

def replayProcess : Process where
  State := Phase
  Identity := Unit
  Trace := Phase
  initial := .protocolFrozen
  step := nextPhase
  identify := fun _ => ()
  emit := fun s => s
  replay := fun t => some t

def replayPassport : Passport replayProcess where
  future_change := by
    intro n
    refine ⟨Nat.succ n, Nat.lt_succ_self n, ?_⟩
    change Not (nextPhase (replayProcess.stateAt n) = replayProcess.stateAt n)
    exact nextPhase_ne_self _
  identity_persists := by
    intro n
    rfl
  trace_replays := by
    intro n
    rfl

def RealizesPrefix
    (P : Process)
    (N : Nat)
    (observed : Fin N -> P.Trace) : Prop :=
  forall i, P.replay (observed i) = some (P.stateAt i.val)

def canonicalPrefix (P : Process) (N : Nat) : Fin N -> P.Trace :=
  fun i => P.emit (P.stateAt i.val)

theorem canonicalPrefix_realizes
    {P : Process}
    (hP : Passport P)
    (N : Nat) :
    RealizesPrefix P N (canonicalPrefix P N) := by
  intro i
  exact hP.trace_replays i.val

def boundedRun : Fin 4 -> replayProcess.Trace :=
  canonicalPrefix replayProcess 4

theorem boundedRun_realizes :
    RealizesPrefix replayProcess 4 boundedRun :=
  canonicalPrefix_realizes replayPassport 4

def stationaryProcess : Process where
  State := Unit
  Identity := Unit
  Trace := Unit
  initial := ()
  step := fun s => s
  identify := fun _ => ()
  emit := fun _ => ()
  replay := fun _ => some ()

def stationaryObservation (N : Nat) : Fin N -> stationaryProcess.Trace :=
  fun _ => ()

theorem stationary_stateAt (n : Nat) : stationaryProcess.stateAt n = () := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Process.stateAt_succ]
      exact ih

theorem stationary_prefix_realizes (N : Nat) :
    RealizesPrefix stationaryProcess N (stationaryObservation N) := by
  intro i
  change some () = some (stationaryProcess.stateAt i.val)
  rw [stationary_stateAt]
  rfl

theorem stationary_not_passport : Not (Passport stationaryProcess) := by
  intro h
  obtain ⟨m, _, hne⟩ := h.future_change 0
  apply hne
  rw [stationary_stateAt, stationary_stateAt]

theorem red_boundary_finite_prefix_not_life (N : Nat) :
    exists P : Process, exists observed : Fin N -> P.Trace,
      RealizesPrefix P N observed ∧ Not (Passport P) := by
  refine ⟨stationaryProcess, stationaryObservation N, ?_, stationary_not_passport⟩
  exact stationary_prefix_realizes N

#print axioms replayPassport
#print axioms boundedRun_realizes
#print axioms red_boundary_finite_prefix_not_life

end DL02
end DigitalLifePassport
