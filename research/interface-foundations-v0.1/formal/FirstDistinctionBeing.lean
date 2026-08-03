import Std

namespace FirstDistinctionBeing

universe u v

abbrev Distinguishability (S : Type u) := S -> S -> Nat

def Distinction {S : Type u} (D : Distinguishability S) (a b : S) : Prop :=
  0 < D a b

def AbsoluteMerge {S : Type u} (D : Distinguishability S) (a b : S) : Prop :=
  D a b = 0

def PlanckTouch {S : Type u} (D : Distinguishability S) (epsilon : Nat) (a b : S) : Prop :=
  0 < D a b ∧ D a b <= epsilon

def Interface {S : Type u} (D : Distinguishability S) (epsilon : Nat) (a b : S) : Prop :=
  epsilon < D a b

def BeingAt {S : Type u} (D : Distinguishability S) (epsilon : Nat) (a b : S) : Prop :=
  Interface D epsilon a b

def EventPossible {S : Type u} (D : Distinguishability S) (a b : S) : Prop :=
  Distinction D a b

def GlobalIndistinguishability {S : Type u} (D : Distinguishability S) : Prop :=
  ∀ x y, D x y = 0

theorem interface_is_distinction
    {S : Type u} (D : Distinguishability S) (epsilon : Nat) (a b : S)
    (visible : Interface D epsilon a b) : Distinction D a b := by
  unfold Interface at visible
  unfold Distinction
  omega

theorem being_excludes_absolute_merge
    {S : Type u} (D : Distinguishability S) (epsilon : Nat) (a b : S)
    (being : BeingAt D epsilon a b) : ¬ AbsoluteMerge D a b := by
  intro merged
  have positive : 0 < D a b := interface_is_distinction D epsilon a b being
  rw [merged] at positive
  exact (Nat.lt_irrefl 0) positive

theorem interface_excludes_planck_touch
    {S : Type u} (D : Distinguishability S) (epsilon : Nat) (a b : S)
    (visible : Interface D epsilon a b) : ¬ PlanckTouch D epsilon a b := by
  intro touch
  exact (Nat.not_lt_of_ge touch.2) visible

theorem planck_touch_excludes_absolute_merge
    {S : Type u} (D : Distinguishability S) (epsilon : Nat) (a b : S)
    (touch : PlanckTouch D epsilon a b) : ¬ AbsoluteMerge D a b := by
  intro merged
  unfold PlanckTouch at touch
  unfold AbsoluteMerge at merged
  rw [merged] at touch
  exact (Nat.lt_irrefl 0) touch.1

theorem witnessed_event_refutes_global_indistinguishability
    {S : Type u} (D : Distinguishability S) (a b : S)
    (event : EventPossible D a b) : ¬ GlobalIndistinguishability D := by
  intro allMerged
  unfold EventPossible Distinction at event
  unfold GlobalIndistinguishability at allMerged
  have merged : D a b = 0 := allMerged a b
  rw [merged] at event
  exact (Nat.lt_irrefl 0) event

abbrev Realizable (S : Type u) := S -> S -> Prop

def PhysicalGuard {S : Type u}
    (D : Distinguishability S) (realizable : Realizable S) (epsilon : Nat) : Prop :=
  ∀ a b, realizable a b -> epsilon < D a b

theorem physical_guard_excludes_planck_touch
    {S : Type u} (D : Distinguishability S) (realizable : Realizable S)
    (epsilon : Nat) (guard : PhysicalGuard D realizable epsilon)
    (a b : S) (physical : realizable a b) : ¬ PlanckTouch D epsilon a b := by
  exact interface_excludes_planck_touch D epsilon a b (guard a b physical)

abbrev Evolution (T : Type v) (S : Type u) := T -> S -> Prop

def DeathAt {T : Type v} {S : Type u}
    (alive : Evolution T S) (before after : T) (x : S) : Prop :=
  alive before x ∧ ¬ alive after x

def AbsoluteNonBeing (S : Type u) : Prop :=
  ∀ x : S, False

theorem death_presupposes_a_state
    {T : Type v} {S : Type u} (alive : Evolution T S)
    (before after : T) (x : S) (_death : DeathAt alive before after x) : Nonempty S := by
  exact ⟨x⟩

theorem death_is_not_absolute_nonbeing
    {T : Type v} {S : Type u} (alive : Evolution T S)
    (before after : T) (x : S) (_death : DeathAt alive before after x) :
    ¬ AbsoluteNonBeing S := by
  intro empty
  exact empty x

end FirstDistinctionBeing

#print axioms FirstDistinctionBeing.interface_is_distinction
#print axioms FirstDistinctionBeing.being_excludes_absolute_merge
#print axioms FirstDistinctionBeing.interface_excludes_planck_touch
#print axioms FirstDistinctionBeing.planck_touch_excludes_absolute_merge
#print axioms FirstDistinctionBeing.witnessed_event_refutes_global_indistinguishability
#print axioms FirstDistinctionBeing.physical_guard_excludes_planck_touch
#print axioms FirstDistinctionBeing.death_presupposes_a_state
#print axioms FirstDistinctionBeing.death_is_not_absolute_nonbeing
