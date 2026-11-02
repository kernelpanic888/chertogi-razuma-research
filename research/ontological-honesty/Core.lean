import Std
namespace OH01
abbrev World := Fin 4
abbrev Region := World → Bool
inductive Status where
  | incompatible | confirmed | refuted | undetermined
  deriving DecidableEq, Repr

abbrev Nonempty (E : Region) : Prop := ∃ w, E w = true
abbrev Supports (E P : Region) : Prop := ∀ w, E w = true → P w = true
abbrev Rejects (E P : Region) : Prop := ∀ w, E w = true → P w = false

def status (E P : Region) : Status :=
  if Nonempty E then
    if Supports E P then .confirmed
    else if Rejects E P then .refuted else .undetermined
  else .incompatible

theorem incompatible_iff (E P : Region) :
    status E P = .incompatible ↔ ¬ Nonempty E := by
  by_cases hn : Nonempty E <;> by_cases hs : Supports E P <;> by_cases hr : Rejects E P
  all_goals simp [status, hn, hs, hr]
  all_goals grind

theorem confirmed_iff (E P : Region) :
    status E P = .confirmed ↔ Nonempty E ∧ Supports E P := by
  by_cases hn : Nonempty E <;> by_cases hs : Supports E P <;> by_cases hr : Rejects E P
  all_goals simp [status, hn, hs, hr]
  all_goals grind

theorem refuted_iff (E P : Region) :
    status E P = .refuted ↔ Nonempty E ∧ Rejects E P := by
  have disjoint : Nonempty E → Supports E P → Rejects E P → False := by
    intro ⟨w, hw⟩ hs hr
    have := hs w hw
    have := hr w hw
    grind
  by_cases hn : Nonempty E <;> by_cases hs : Supports E P <;> by_cases hr : Rejects E P
  all_goals simp [status, hn, hs, hr]
  all_goals grind

theorem undetermined_iff (E P : Region) :
    status E P = .undetermined ↔
      (∃ w, E w = true ∧ P w = true) ∧ (∃ w, E w = true ∧ P w = false) := by
  simp only [status, Nonempty, Supports, Rejects]
  repeat first | split
  all_goals simp_all
  all_goals grind

theorem complete (E P : Region) :
    status E P = .incompatible ∨ status E P = .confirmed ∨
    status E P = .refuted ∨ status E P = .undetermined := by
  cases status E P <;> simp

theorem exclusive (E P : Region) (s t : Status)
    (hs : status E P = s) (ht : status E P = t) : s = t := hs.symm.trans ht

theorem confirmed_refinement (E F P : Region)
    (h : status E P = .confirmed) (hn : Nonempty F)
    (sub : ∀ w, F w = true → E w = true) : status F P = .confirmed := by
  apply (confirmed_iff F P).mpr
  exact ⟨hn, fun w hw => ((confirmed_iff E P).mp h).2 w (sub w hw)⟩

theorem refuted_refinement (E F P : Region)
    (h : status E P = .refuted) (hn : Nonempty F)
    (sub : ∀ w, F w = true → E w = true) : status F P = .refuted := by
  apply (refuted_iff F P).mpr
  exact ⟨hn, fun w hw => ((refuted_iff E P).mp h).2 w (sub w hw)⟩

def singleton (w : World) : Region := fun v => decide (v = w)

theorem resolve_uncertainty (E P : Region) (h : status E P = .undetermined) :
    (∃ w, E w = true ∧ status (singleton w) P = .confirmed) ∧
    (∃ w, E w = true ∧ status (singleton w) P = .refuted) := by
  obtain ⟨⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩⟩ := (undetermined_iff E P).mp h
  constructor
  · refine ⟨a, ha, (confirmed_iff _ _).mpr ?_⟩
    simp [Nonempty, Supports, singleton, hpa]
  · refine ⟨b, hb, (refuted_iff _ _).mpr ?_⟩
    simp [Nonempty, Rejects, singleton, hpb]

theorem rename_invariant (E P : Region) (f g : World → World)
    (_hfg : ∀ w, f (g w) = w) (hgf : ∀ w, g (f w) = w) :
    status (fun w => E (g w)) (fun w => P (g w)) = status E P := by
  have hn : Nonempty (fun w => E (g w)) ↔ Nonempty E := by
    constructor
    · rintro ⟨w, hw⟩; exact ⟨g w, hw⟩
    · rintro ⟨w, hw⟩; exact ⟨f w, by simpa [hgf] using hw⟩
  have hs : Supports (fun w => E (g w)) (fun w => P (g w)) ↔ Supports E P := by
    constructor
    · intro h w hw; simpa [hgf] using h (f w) (by simpa [hgf] using hw)
    · intro h w hw; exact h (g w) hw
  have hr : Rejects (fun w => E (g w)) (fun w => P (g w)) ↔ Rejects E P := by
    constructor
    · intro h w hw; simpa [hgf] using h (f w) (by simpa [hgf] using hw)
    · intro h w hw; exact h (g w) hw
  simp only [status, hn, hs, hr]

end OH01
