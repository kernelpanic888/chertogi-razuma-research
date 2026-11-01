import Std
set_option autoImplicit false
namespace ER01

/-- Exact rational input: rho=diag(p/q,1-p/q), C=diag(1,l/d). See weights:
    branch zero is unchanged, branch one receives (l/d)^2. -/
structure Config where
  p : Nat
  q : Nat
  l : Nat
  d : Nat
  q_pos : 0 < q
  d_pos : 0 < d
  p_le : p ≤ q
  l_le : l ≤ d

/-- Unnormalised integer masses, with common denominator q*d^2. -/
structure Mass where
  zero : Nat
  one : Nat
  deriving Repr, BEq, DecidableEq

def Mass.total (m : Mass) : Nat := m.zero + m.one

def weights (c : Config) : Mass :=
  ⟨c.p * c.d ^ 2, c.l ^ 2 * (c.q - c.p)⟩

def commonDenominator (c : Config) : Nat := c.q * c.d ^ 2

/-- Canonical unreduced fraction; denominator is always positive.
    No floating point or division occurs in the trusted transition engine. -/
structure Probability where
  numerator : Nat
  denominator : Nat
  positive : 0 < denominator
  bounded : numerator ≤ denominator

def posterior (m : Mass) : Option Probability :=
  if h : 0 < m.total then
    some ⟨m.zero, m.total, h, Nat.le_add_right m.zero m.one⟩
  else none

theorem posterior_none_iff (m : Mass) : posterior m = none ↔ m.total = 0 := by
  unfold posterior
  split <;> simp_all <;> omega

theorem posterior_exists_iff (m : Mass) :
    (∃ r, posterior m = some r) ↔ 0 < m.total := by
  unfold posterior
  split <;> simp_all

theorem branch_mass_conservation (m : Mass) :
    m.zero + m.one = m.total := rfl

theorem positive_mass_iff (m : Mass) :
    0 < m.total ↔ 0 < m.zero ∨ 0 < m.one := by
  unfold Mass.total; omega

theorem normalization_bounds {m : Mass} {r : Probability}
    (_h : posterior m = some r) : r.numerator ≤ r.denominator := r.bounded

theorem normalization_denominator {m : Mass} {r : Probability}
    (h : posterior m = some r) : r.denominator = m.total := by
  unfold posterior at h
  split at h
  · cases h; rfl
  · contradiction

inductive Phase where
  | prepared | filtered | admitted | observed | returned | rejected
  deriving Repr, BEq, DecidableEq

structure Frame where
  tick : Nat
  phase : Phase
  mass : Mass
  deriving Repr, BEq, DecidableEq

/-- The global ensemble is retained even after conditional observation. -/
def initial (c : Config) : Frame := ⟨0, .prepared, ⟨c.p, c.q - c.p⟩⟩

def step (c : Config) (s : Frame) : Frame :=
  match s.phase with
  | .prepared => ⟨s.tick + 1, .filtered, weights c⟩
  | .filtered => ⟨s.tick + 1, if s.mass.total = 0 then .rejected else .admitted, s.mass⟩
  | .admitted => ⟨s.tick + 1, .observed, s.mass⟩
  | .observed => ⟨s.tick + 1, .returned, s.mass⟩
  | .returned | .rejected => s

def evolve (c : Config) : Nat → Frame
  | 0 => initial c
  | n + 1 => step c (evolve c n)

def trace (c : Config) (steps : Nat) : List Frame :=
  (List.range (steps + 1)).map (evolve c)

theorem step_tick_monotone (c : Config) (s : Frame) :
    s.tick ≤ (step c s).tick := by
  cases s with | mk t p m => cases p <;> simp [step] <;> omega

theorem returned_is_fixed (c : Config) (s : Frame) (h : s.phase = .returned) :
    step c s = s := by simp [step, h]

theorem rejected_is_fixed (c : Config) (s : Frame) (h : s.phase = .rejected) :
    step c s = s := by simp [step, h]

theorem filtered_mass_retained (c : Config) (s : Frame) (h : s.phase ≠ .prepared) :
    (step c s).mass = s.mass := by
  cases s with | mk t p m => cases p <;> simp_all [step]

theorem zero_rejects (c : Config) (s : Frame)
    (hp : s.phase = .filtered) (hz : s.mass.total = 0) :
    (step c s).phase = .rejected := by simp [step, hp, hz]

theorem positive_admits (c : Config) (s : Frame)
    (hp : s.phase = .filtered) (hz : 0 < s.mass.total) :
    (step c s).phase = .admitted := by
  have hn : s.mass.total ≠ 0 := by omega
  simp [step, hp, hn]

theorem four_steps_close (c : Config) :
    (evolve c 4).phase = .returned ∨ (evolve c 4).phase = .rejected := by
  by_cases h : (weights c).total = 0
  · simp [evolve, initial, step, h]
  · simp [evolve, initial, step, h]

/-- Observability is separate from filtering: a coarse readout merges two
    distinct latent labels; a resolved readout retains them. -/
inductive Mode where | coarse | resolved deriving Repr, BEq

def read (mode : Mode) (hidden : Bool) : Nat :=
  match mode with
  | .coarse => 0
  | .resolved => if hidden then 1 else 0

theorem coarse_indistinguishable : read .coarse false = read .coarse true := rfl

theorem resolved_distinguishable : read .resolved false ≠ read .resolved true := by decide

theorem coarse_not_injective : ¬ Function.Injective (read .coarse) := by
  intro h
  have hf : false = true := h coarse_indistinguishable
  cases hf

/-- A display readout never changes the physical/model ensemble. -/
def observation (mode : Mode) (m : Mass) : List (Nat × Nat) :=
  match mode with
  | .coarse => [(0, m.total)]
  | .resolved => [(0, m.zero), (1, m.one)]

theorem observation_mass_conserved (mode : Mode) (m : Mass) :
    ((observation mode m).map Prod.snd).sum = m.total := by
  cases mode <;> simp [observation, Mass.total]

theorem coarse_observation_only_total (m n : Mass) (h : m.total = n.total) :
    observation .coarse m = observation .coarse n := by
  simp [observation, h]

theorem denominator_positive (c : Config) : 0 < commonDenominator c :=
  Nat.mul_pos c.q_pos (Nat.pow_pos c.d_pos)

theorem filter_does_not_create_mass (c : Config) :
    (weights c).total ≤ commonDenominator c := by
  have hsq := Nat.pow_le_pow_left c.l_le 2
  have hb := Nat.mul_le_mul_right (c.q - c.p) hsq
  have heq : c.p + (c.q - c.p) = c.q := by
    have hp := c.p_le
    omega
  unfold weights Mass.total commonDenominator
  calc
    c.p * c.d ^ 2 + c.l ^ 2 * (c.q - c.p)
        ≤ c.p * c.d ^ 2 + c.d ^ 2 * (c.q - c.p) := Nat.add_le_add_left hb _
    _ = (c.p + (c.q - c.p)) * c.d ^ 2 := by
      rw [Nat.add_mul, Nat.mul_comm (c.q - c.p)]
    _ = c.q * c.d ^ 2 := by rw [heq]

/-- Reachable admitted/observed/returned states always have positive mass. -/
def Valid (s : Frame) : Prop :=
  (s.phase = .admitted ∨ s.phase = .observed ∨ s.phase = .returned) → 0 < s.mass.total

theorem initial_valid (c : Config) : Valid (initial c) := by
  simp [Valid, initial]

theorem step_valid (c : Config) (s : Frame) (hs : Valid s) : Valid (step c s) := by
  cases s with
  | mk t p m =>
    cases p <;> simp_all [Valid, step]
    split <;> simp_all <;> omega

theorem evolve_valid (c : Config) (n : Nat) : Valid (evolve c n) := by
  induction n with
  | zero => exact initial_valid c
  | succ n ih => exact step_valid c (evolve c n) ih

theorem reachable_observation_has_posterior (c : Config) (n : Nat)
    (h : (evolve c n).phase = .observed ∨ (evolve c n).phase = .returned) :
    ∃ r, posterior (evolve c n).mass = some r := by
  apply (posterior_exists_iff _).mpr
  apply evolve_valid c n
  rcases h with ho | hr
  · exact Or.inr (Or.inl ho)
  · exact Or.inr (Or.inr hr)

end ER01
