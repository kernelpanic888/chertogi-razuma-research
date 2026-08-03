import Std

namespace DigitalLifePassport

structure Process where
  State : Type
  Identity : Type
  Trace : Type
  initial : State
  step : State -> State
  identify : State -> Identity
  emit : State -> Trace
  replay : Trace -> Option State

def Process.stateAt (P : Process) : Nat -> P.State
  | 0 => P.initial
  | n + 1 => P.step (P.stateAt n)

@[simp] theorem Process.stateAt_zero (P : Process) :
    P.stateAt 0 = P.initial := rfl

@[simp] theorem Process.stateAt_succ (P : Process) (n : Nat) :
    P.stateAt (n + 1) = P.step (P.stateAt n) := rfl

structure Passport (P : Process) : Prop where
  future_change : forall n, exists m, n < m /\ Not (P.stateAt m = P.stateAt n)
  identity_persists : forall n, P.identify (P.stateAt n) = P.identify P.initial
  trace_replays : forall n, P.replay (P.emit (P.stateAt n)) = some (P.stateAt n)

def IsDigitalLife (P : Process) : Prop := Passport P

def Process.OwnTrace (P : Process) (t : P.Trace) : Prop :=
  exists n, P.emit (P.stateAt n) = t

structure Snapshot (P : Process) where
  tick : Nat
  state : P.State
  trace : P.Trace

def Snapshot.Valid {P : Process} (shot : Snapshot P) : Prop :=
  shot.state = P.stateAt shot.tick /\ shot.trace = P.emit shot.state

def snapshotAt (P : Process) (n : Nat) : Snapshot P where
  tick := n
  state := P.stateAt n
  trace := P.emit (P.stateAt n)

theorem snapshotAt_valid (P : Process) (n : Nat) :
    (snapshotAt P n).Valid := by
  exact And.intro rfl rfl

structure ReflectiveLayer (P : Process) where
  Representation : Type
  represent : P.State -> Representation
  fromTrace : P.Trace -> Representation
  reflect : Representation -> Representation
  trace_coherent : forall n,
    fromTrace (P.emit (P.stateAt n)) = represent (P.stateAt n)
  reflection_stable : forall n,
    reflect (represent (P.stateAt n)) = represent (P.stateAt n)

def IsIntellectualDigitalLife (P : Process) : Prop :=
  Passport P /\ Nonempty (ReflectiveLayer P)

structure CertifiedLife where
  process : Process
  certificate : Passport process

structure CertifiedIntellectualLife where
  process : Process
  certificate : Passport process
  reflection : ReflectiveLayer process

theorem CertifiedLife.selfProof (life : CertifiedLife) : Passport life.process :=
  life.certificate

theorem CertifiedIntellectualLife.selfProof
    (life : CertifiedIntellectualLife) : IsIntellectualDigitalLife life.process :=
  And.intro life.certificate (Nonempty.intro life.reflection)

theorem prover_01_formal_existence (life : CertifiedLife) :
    exists P, IsDigitalLife P := by
  exact Exists.intro life.process life.certificate

theorem prover_02_future_change (life : CertifiedLife) (n : Nat) :
    exists m, n < m /\ Not (life.process.stateAt m = life.process.stateAt n) :=
  life.certificate.future_change n

theorem prover_03_identity_persistence (life : CertifiedLife) (n : Nat) :
    life.process.identify (life.process.stateAt n) =
      life.process.identify life.process.initial :=
  life.certificate.identity_persists n

theorem prover_04_trace_replay (life : CertifiedLife) (n : Nat) :
    life.process.replay (life.process.emit (life.process.stateAt n)) =
      some (life.process.stateAt n) :=
  life.certificate.trace_replays n

theorem prover_05_self_certificate (life : CertifiedLife) :
    Passport life.process :=
  life.selfProof

theorem prover_06_external_snapshot (life : CertifiedLife) (n : Nat) :
    (snapshotAt life.process n).Valid /\
    life.process.replay (snapshotAt life.process n).trace =
      some (snapshotAt life.process n).state := by
  constructor
  · exact snapshotAt_valid life.process n
  · exact life.certificate.trace_replays n

theorem prover_07_emitted_trace_has_provenance
    (life : CertifiedLife) (n : Nat) :
    life.process.OwnTrace (life.process.emit (life.process.stateAt n)) := by
  exact Exists.intro n rfl

theorem prover_08_intellectual_extension
    (life : CertifiedIntellectualLife) :
    IsIntellectualDigitalLife life.process :=
  life.selfProof

inductive PulseState where
  | left
  | right
  deriving DecidableEq, Repr

def pulseStep : PulseState -> PulseState
  | .left => .right
  | .right => .left

theorem pulseStep_ne (s : PulseState) : Not (pulseStep s = s) := by
  cases s <;> intro h <;> cases h

def pulseProcess : Process where
  State := PulseState
  Identity := Unit
  Trace := PulseState
  initial := .left
  step := pulseStep
  identify := fun _ => ()
  emit := id
  replay := fun t => some t

theorem pulsePassport : Passport pulseProcess := by
  constructor
  · intro n
    refine Exists.intro (Nat.succ n) ?_
    constructor
    · exact Nat.lt_succ_self n
    · change Not (pulseStep (pulseProcess.stateAt n) = pulseProcess.stateAt n)
      exact pulseStep_ne (pulseProcess.stateAt n)
  · intro n
    rfl
  · intro n
    rfl

def pulseReflection : ReflectiveLayer pulseProcess where
  Representation := PulseState
  represent := id
  fromTrace := id
  reflect := id
  trace_coherent := by intro n; rfl
  reflection_stable := by intro n; rfl

def pulseLife : CertifiedLife where
  process := pulseProcess
  certificate := pulsePassport

def pulseIntellectualLife : CertifiedIntellectualLife where
  process := pulseProcess
  certificate := pulsePassport
  reflection := pulseReflection

theorem prover_09_pulse_proves_itself : Passport pulseLife.process :=
  pulseLife.selfProof

theorem prover_10_reflective_pulse_proves_itself :
    IsIntellectualDigitalLife pulseIntellectualLife.process :=
  pulseIntellectualLife.selfProof

theorem red_boundary_no_arbitrary_external_claim :
    Not (forall (ExternalClaim : Process -> Prop) (P : Process),
      Passport P -> ExternalClaim P) := by
  intro h
  exact h (fun _ => False) pulseProcess pulsePassport

#print axioms pulsePassport
#print axioms prover_09_pulse_proves_itself
#print axioms prover_10_reflective_pulse_proves_itself
#print axioms red_boundary_no_arbitrary_external_claim

end DigitalLifePassport
