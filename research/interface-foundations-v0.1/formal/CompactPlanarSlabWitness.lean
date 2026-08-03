import SummableCompactTentWitness

namespace BoundaryOfSelf
namespace CompactPlanarSlabWitness

noncomputable section

open Filter
open Set
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open ControlledEquivComposition
open FiniteControlledChain
open TwoSidedLimitHomeomorph
open CompactTentHomeomorphism
open SummableCompactTentWitness

abbrev CrossSection := Set.Icc (-1 : Real) 1

abbrev PlanarSlab := Real × CrossSection

def liftHomeomorph (homeomorph : Real ≃ₜ Real) : PlanarSlab ≃ₜ PlanarSlab where
  toEquiv :=
    { toFun := fun point => (homeomorph point.1, point.2)
      invFun := fun point => (homeomorph.symm point.1, point.2)
      left_inv := fun point => by
        ext <;> simp
      right_inv := fun point => by
        ext <;> simp }
  continuous_toFun :=
    (homeomorph.continuous.comp continuous_fst).prodMk continuous_snd
  continuous_invFun :=
    (homeomorph.symm.continuous.comp continuous_fst).prodMk continuous_snd

@[simp]
theorem liftHomeomorph_apply (homeomorph : Real ≃ₜ Real) (point : PlanarSlab) :
    liftHomeomorph homeomorph point = (homeomorph point.1, point.2) := rfl

@[simp]
theorem liftHomeomorph_symm_apply (homeomorph : Real ≃ₜ Real)
    (point : PlanarSlab) :
    (liftHomeomorph homeomorph).symm point =
      (homeomorph.symm point.1, point.2) := rfl

def liftControlled
    (controlled : ControlledEquiv Real Real)
    (hForwardOne : 1 <= (controlled.forwardConstant : Real))
    (hInverseOne : 1 <= (controlled.inverseConstant : Real)) :
    ControlledEquiv PlanarSlab PlanarSlab where
  toHomeomorph := liftHomeomorph controlled.toHomeomorph
  forwardConstant := controlled.forwardConstant
  inverseConstant := controlled.inverseConstant
  forward_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    change max (dist (controlled first.1) (controlled second.1))
        (dist first.2 second.2) <=
      (controlled.forwardConstant : Real) *
        max (dist first.1 second.1) (dist first.2 second.2)
    apply max_le
    · calc
        dist (controlled first.1) (controlled second.1) <=
            (controlled.forwardConstant : Real) * dist first.1 second.1 :=
          controlled.forward_lipschitz.dist_le_mul first.1 second.1
        _ <= (controlled.forwardConstant : Real) *
            max (dist first.1 second.1) (dist first.2 second.2) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (NNReal.coe_nonneg _)
    · calc
        dist first.2 second.2 <=
            max (dist first.1 second.1) (dist first.2 second.2) := le_max_right _ _
        _ = 1 * max (dist first.1 second.1) (dist first.2 second.2) := by ring
        _ <= (controlled.forwardConstant : Real) *
            max (dist first.1 second.1) (dist first.2 second.2) :=
          mul_le_mul_of_nonneg_right hForwardOne (by positivity)
  inverse_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    change max
        (dist (controlled.toHomeomorph.symm first.1)
          (controlled.toHomeomorph.symm second.1))
        (dist first.2 second.2) <=
      (controlled.inverseConstant : Real) *
        max (dist first.1 second.1) (dist first.2 second.2)
    apply max_le
    · calc
        dist (controlled.toHomeomorph.symm first.1)
            (controlled.toHomeomorph.symm second.1) <=
          (controlled.inverseConstant : Real) * dist first.1 second.1 :=
            controlled.inverse_lipschitz.dist_le_mul first.1 second.1
        _ <= (controlled.inverseConstant : Real) *
            max (dist first.1 second.1) (dist first.2 second.2) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (NNReal.coe_nonneg _)
    · calc
        dist first.2 second.2 <=
            max (dist first.1 second.1) (dist first.2 second.2) := le_max_right _ _
        _ = 1 * max (dist first.1 second.1) (dist first.2 second.2) := by ring
        _ <= (controlled.inverseConstant : Real) *
            max (dist first.1 second.1) (dist first.2 second.2) :=
          mul_le_mul_of_nonneg_right hInverseOne (by positivity)

@[simp]
theorem liftControlled_apply
    (controlled : ControlledEquiv Real Real)
    (hForwardOne : 1 <= (controlled.forwardConstant : Real))
    (hInverseOne : 1 <= (controlled.inverseConstant : Real))
    (point : PlanarSlab) :
    liftControlled controlled hForwardOne hInverseOne point =
      (controlled point.1, point.2) := rfl

theorem localTentStep_forward_one (n : Nat) :
    1 <= ((localTentSequence n).forwardConstant : Real) := by
  change 1 <= ((((1 + localAmplitude (n + 1)) /
    (1 + localAmplitude n)).toNNReal : NNReal) : Real)
  rw [Real.coe_toNNReal _ (div_nonneg
    (by linarith [localAmplitude_nonnegative (n + 1)])
    (by linarith [localAmplitude_nonnegative n]))]
  apply (le_div_iff₀ (by linarith [localAmplitude_nonnegative n] :
    0 < 1 + localAmplitude n)).2
  linarith [localAmplitude_mono_step n]

theorem localTentStep_inverse_one (n : Nat) :
    1 <= ((localTentSequence n).inverseConstant : Real) := by
  change 1 <= ((((1 - localAmplitude n) /
    (1 - localAmplitude (n + 1))).toNNReal : NNReal) : Real)
  rw [Real.coe_toNNReal _ (div_nonneg
    (by linarith [localAmplitude_lt_one n])
    (by linarith [localAmplitude_lt_one (n + 1)]))]
  apply (le_div_iff₀ (by linarith [localAmplitude_lt_one (n + 1)] :
    0 < 1 - localAmplitude (n + 1))).2
  linarith [localAmplitude_mono_step n]

def planarSequence (n : Nat) : ControlledEquiv PlanarSlab PlanarSlab :=
  liftControlled (localTentSequence n)
    (localTentStep_forward_one n) (localTentStep_inverse_one n)

def limitPlanarHomeomorph : PlanarSlab ≃ₜ PlanarSlab :=
  liftHomeomorph limitLocalTent

theorem prefix_planar_apply (n : Nat) (point : PlanarSlab) :
    prefixControlledEquiv planarSequence n point =
      (prefixControlledEquiv localTentSequence n point.1, point.2) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      change planarSequence n
          (prefixControlledEquiv planarSequence n point) =
        (localTentSequence n
          (prefixControlledEquiv localTentSequence n point.1), point.2)
      rw [inductionHypothesis]
      rfl

theorem prefix_planar_inverse_apply (n : Nat) (point : PlanarSlab) :
    (prefixControlledEquiv planarSequence n).toHomeomorph.symm point =
      ((prefixControlledEquiv localTentSequence n).toHomeomorph.symm point.1,
        point.2) := by
  apply (prefixControlledEquiv planarSequence n).toHomeomorph.injective
  rw [(prefixControlledEquiv planarSequence n).toHomeomorph.apply_symm_apply]
  rw [prefix_planar_apply]
  simp

theorem prefix_planar_forwardConstant (n : Nat) :
    (prefixControlledEquiv planarSequence n).forwardConstant =
      (prefixControlledEquiv localTentSequence n).forwardConstant := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      change (localTentSequence n).forwardConstant *
          (prefixControlledEquiv planarSequence n).forwardConstant =
        (localTentSequence n).forwardConstant *
          (prefixControlledEquiv localTentSequence n).forwardConstant
      rw [inductionHypothesis]

theorem prefix_planar_inverseConstant (n : Nat) :
    (prefixControlledEquiv planarSequence n).inverseConstant =
      (prefixControlledEquiv localTentSequence n).inverseConstant := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      change (prefixControlledEquiv planarSequence n).inverseConstant *
          (localTentSequence n).inverseConstant =
        (prefixControlledEquiv localTentSequence n).inverseConstant *
          (localTentSequence n).inverseConstant
      rw [inductionHypothesis]

theorem prefix_planar_forward_bound (n : Nat) :
    ((prefixControlledEquiv planarSequence n).forwardConstant : Real) <= 3 / 2 := by
  rw [prefix_planar_forwardConstant]
  exact prefix_localTent_forward_bound n

theorem prefix_planar_inverse_bound (n : Nat) :
    ((prefixControlledEquiv planarSequence n).inverseConstant : Real) <= 2 := by
  rw [prefix_planar_inverseConstant]
  exact prefix_localTent_inverse_bound n

theorem prefix_planar_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point => prefixControlledEquiv planarSequence n point)
      limitPlanarHomeomorph atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hOneDimensional :=
    (Metric.tendstoUniformlyOn_iff.mp prefix_localTents_tendsto_uniformly)
      epsilon hEpsilon
  filter_upwards [hOneDimensional] with n hN
  intro point _
  have hPoint := hN point.1 (mem_univ point.1)
  rw [prefix_planar_apply]
  change max
      (dist (limitLocalTent point.1)
        (prefixControlledEquiv localTentSequence n point.1))
      (dist point.2 point.2) < epsilon
  simpa using hPoint

theorem inverse_prefix_planar_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point =>
        (prefixControlledEquiv planarSequence n).toHomeomorph.symm point)
      limitPlanarHomeomorph.symm atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hOneDimensional :=
    (Metric.tendstoUniformlyOn_iff.mp inverse_prefix_localTents_tendsto_uniformly)
      epsilon hEpsilon
  filter_upwards [hOneDimensional] with n hN
  intro point _
  have hPoint := hN point.1 (mem_univ point.1)
  rw [prefix_planar_inverse_apply]
  change max
      (dist (limitLocalTent.symm point.1)
        ((prefixControlledEquiv localTentSequence n).toHomeomorph.symm point.1))
      (dist point.2 point.2) < epsilon
  simpa using hPoint

def planarSupport : Set PlanarSlab :=
  Set.Icc (-1 : Real) 1 ×ˢ Set.univ

theorem planarSupport_compact : IsCompact planarSupport := by
  exact isCompact_Icc.prod isCompact_univ

theorem first_abs_ge_one_of_not_mem_support
    {point : PlanarSlab} (hPoint : point ∉ planarSupport) :
    1 <= |point.1| := by
  by_contra hAbs
  have hAbsLt : |point.1| < 1 := lt_of_not_ge hAbs
  have hFirstMem : point.1 ∈ Set.Icc (-1 : Real) 1 := by
    constructor
    · linarith [neg_abs_le point.1]
    · linarith [le_abs_self point.1]
  exact hPoint ⟨hFirstMem, mem_univ point.2⟩

theorem prefix_planar_identity_outside
    (n : Nat) {point : PlanarSlab} (hPoint : point ∉ planarSupport) :
    prefixControlledEquiv planarSequence n point = point := by
  rw [prefix_planar_apply]
  apply Prod.ext
  · rw [prefix_localTent_apply, localTentPrefix_apply]
    simp [tentMap,
      tentBump_eq_zero_of_abs_ge_one
        (first_abs_ge_one_of_not_mem_support hPoint)]
  · rfl

theorem limit_planar_identity_outside
    {point : PlanarSlab} (hPoint : point ∉ planarSupport) :
    limitPlanarHomeomorph point = point := by
  apply Prod.ext
  · change limitLocalTent point.1 = point.1
    exact limit_tent_is_local (first_abs_ge_one_of_not_mem_support hPoint)
  · rfl

theorem planar_step_identity_outside
    (n : Nat) {point : PlanarSlab} (hPoint : point ∉ planarSupport) :
    planarSequence n point = point := by
  have hCurrent : localTentPrefix n point.1 = point.1 := by
    rw [localTentPrefix_apply]
    simp [tentMap,
      tentBump_eq_zero_of_abs_ge_one
        (first_abs_ge_one_of_not_mem_support hPoint)]
  have hNext : localTentPrefix (n + 1) point.1 = point.1 := by
    rw [localTentPrefix_apply]
    simp [tentMap,
      tentBump_eq_zero_of_abs_ge_one
        (first_abs_ge_one_of_not_mem_support hPoint)]
  have hCurrentInverse :
      (localTentPrefix n).toHomeomorph.symm point.1 = point.1 := by
    apply (localTentPrefix n).toHomeomorph.injective
    rw [(localTentPrefix n).toHomeomorph.apply_symm_apply, hCurrent]
  apply Prod.ext
  · change localTentPrefix (n + 1)
      ((localTentPrefix n).toHomeomorph.symm point.1) = point.1
    rw [hCurrentInverse, hNext]
  · rfl

theorem forward_planar_prefixes_uniformCauchy :
    UniformCauchySeqOn
      (fun n point => prefixControlledEquiv planarSequence n point)
      atTop univ :=
  prefix_planar_tendsto_uniformly.uniformCauchySeqOn

theorem inverse_planar_prefixes_uniformCauchy :
    UniformCauchySeqOn
      (fun n point =>
        (prefixControlledEquiv planarSequence n).toHomeomorph.symm point)
      atTop univ :=
  inverse_prefix_planar_tendsto_uniformly.uniformCauchySeqOn

theorem exists_compact_planar_limit
    (model : ComputableBoundaryModel PlanarSlab) :
    ∃ limitHomeomorph : PlanarSlab ≃ₜ PlanarSlab,
      limitHomeomorph = limitPlanarHomeomorph ∧
      frontier (limitHomeomorph '' model.inside) =
        limitHomeomorph '' model.interface ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          (prefixComputableBoundaryModel planarSequence n model).interface
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          ((prefixComputableBoundaryModel planarSequence n model).approximation.carrier n)
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) := by
  obtain ⟨limitHomeomorph, hForwardLimit, _hInverseLimit,
    hFrontier, hMoving, hComputed⟩ :=
    exists_limit_homeomorph_and_actual_frontier
      planarSequence model forward_planar_prefixes_uniformCauchy
      inverse_planar_prefixes_uniformCauchy (3 / 2) 2
      prefix_planar_forward_bound prefix_planar_inverse_bound
  have hExact : limitHomeomorph = limitPlanarHomeomorph := by
    apply Homeomorph.ext
    intro point
    exact tendsto_nhds_unique
      (hForwardLimit.tendsto_at (mem_univ point))
      (prefix_planar_tendsto_uniformly.tendsto_at (mem_univ point))
  exact ⟨limitHomeomorph, hExact, hFrontier, hMoving, hComputed⟩

end
end CompactPlanarSlabWitness
end BoundaryOfSelf
