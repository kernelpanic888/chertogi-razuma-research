-- Self-Contained Lean 4 Verification Capsule (MI-01 · TMI v0.3)
-- I_{A↔B} = ∂(A,B) ∘ T_{A↔B} | Paste directly into https://live.lean-lang.org/
set_option autoImplicit false
universe u v w uInv

structure Language where
  Left : Type u
  Right : Type v
  Boundary : Type w -- ∂(A,B)
  separated : Left → Right → Prop
  bounds : Boundary → Left → Right → Prop
  reverseContact : Boundary → Right → Left → Prop
  forwardContact : Boundary → Left → Right → Prop

def Language.Visible (L : Language.{u, v, w}) (a : L.Left) (b : L.Right) : Prop :=
  ∃ d : L.Boundary, L.bounds d a b ∧ L.separated a b ∧ L.reverseContact d b a

def Language.Reciprocal (L : Language.{u, v, w}) (a : L.Left) (b : L.Right) : Prop :=
  ∃ d : L.Boundary, L.bounds d a b ∧ L.separated a b ∧
    L.reverseContact d b a ∧ L.forwardContact d a b

def Language.Merged (L : Language.{u, v, w}) (a : L.Left) (b : L.Right) : Prop :=
  ¬ L.separated a b

theorem reciprocal_implies_visible {L : Language.{u, v, w}} {a : L.Left} {b : L.Right}
    (h : L.Reciprocal a b) : L.Visible a b := by
  rcases h with ⟨d, hb, hs, hr, _⟩
  exact ⟨d, hb, hs, hr⟩

theorem visible_implies_separated {L : Language.{u, v, w}} {a : L.Left} {b : L.Right}
    (h : L.Visible a b) : L.separated a b := by
  rcases h with ⟨_, _, hs, _⟩
  exact hs

structure TransportEquiv (α : Type uInv) (β : Type uInv) where -- T_{A↔B}
  toFun : α → β
  invFun : β → α
  leftInverse : ∀ x, invFun (toFun x) = x
  rightInverse : ∀ y, toFun (invFun y) = y

structure CandidateInterface (L : Language.{u, v, w}) (Inv : Type uInv)
    (subject : L.Left) (surface : L.Right) where
  reciprocal : L.Reciprocal subject surface
  project : Inv → Inv
  reflect : Inv → Inv
  distortionError : Nat

def BetterOrEqualInterface {L : Language.{u, v, w}} {Inv : Type uInv} {s : L.Left}
    {r₁ r₂ : L.Right} (C₁ : CandidateInterface L Inv s r₁)
    (C₂ : CandidateInterface L Inv s r₂) : Prop :=
  C₁.distortionError ≤ C₂.distortionError

structure ReflectionInterface (L : Language.{u, v, w}) (Inv : Type uInv)
    (subject : L.Left) (reflection : L.Right) where
  reciprocal : L.Reciprocal subject reflection
  transport  : TransportEquiv Inv Inv

def ReflectionInterface.toCandidate {L : Language.{u, v, w}} {Inv : Type uInv}
    {subject : L.Left} {reflection : L.Right}
    (R : ReflectionInterface L Inv subject reflection) :
    CandidateInterface L Inv subject reflection where
  reciprocal := R.reciprocal
  project := R.transport.toFun
  reflect := R.transport.invFun
  distortionError := 0

-- Synthesized by DeepSeek-Prover-V2-7B + LoRA & verified in Lean 4:
theorem reflection_interface_is_visible
    {L : Language.{u, v, w}} {Inv : Type uInv} {subject : L.Left} {reflection : L.Right}
    (R : ReflectionInterface L Inv subject reflection) : L.Visible subject reflection := by
  exact reciprocal_implies_visible R.reciprocal

theorem reflection_interface_preserves_separation
    {L : Language.{u, v, w}} {Inv : Type uInv} {subject : L.Left} {reflection : L.Right}
    (R : ReflectionInterface L Inv subject reflection) : L.separated subject reflection := by
  exact visible_implies_separated (reflection_interface_is_visible R)

theorem reflection_roundtrip_preserves_invariant
    {L : Language.{u, v, w}} {Inv : Type uInv} {subject : L.Left} {reflection : L.Right}
    (R : ReflectionInterface L Inv subject reflection) (x : Inv) :
    R.toCandidate.reflect (R.toCandidate.project x) = x := by
  exact R.transport.leftInverse x

theorem reflection_is_best_interface
    {L : Language.{u, v, w}} {Inv : Type uInv} {subject : L.Left} {reflection otherSurface : L.Right}
    (R : ReflectionInterface L Inv subject reflection)
    (C : CandidateInterface L Inv subject otherSurface) :
    BetterOrEqualInterface R.toCandidate C := by
  exact Nat.zero_le C.distortionError

-- Red Boundary negative theorems (what we do NOT claim):
theorem reflection_interface_not_merged
    {L : Language.{u, v, w}} {Inv : Type uInv} {subject : L.Left} {reflection : L.Right}
    (R : ReflectionInterface L Inv subject reflection) : ¬ L.Merged subject reflection := by
  intro hMerged
  exact hMerged (reflection_interface_preserves_separation R)

theorem reflection_interface_does_not_imply_second_subject :
    ¬ (∀ (L : Language.{u, v, w}) (Inv : Type uInv) (s : L.Left) (r : L.Right)
      (_ : ReflectionInterface L Inv s r) (SecondSubject : Prop), SecondSubject) := by
  intro h; exact False.elim (h ⟨PUnit, PUnit, PUnit, fun _ _ => True,
    fun _ _ _ => True, fun _ _ _ => True, fun _ _ _ => True⟩ PUnit
    PUnit.unit PUnit.unit ⟨⟨PUnit.unit, trivial, trivial, trivial, trivial⟩,
    ⟨id, id, fun _ => rfl, fun _ => rfl⟩⟩ False)

#print axioms reciprocal_implies_visible
#print axioms visible_implies_separated
#print axioms reflection_interface_is_visible
#print axioms reflection_interface_preserves_separation
#print axioms reflection_roundtrip_preserves_invariant
#print axioms reflection_is_best_interface
#print axioms reflection_interface_not_merged
#print axioms reflection_interface_does_not_imply_second_subject
