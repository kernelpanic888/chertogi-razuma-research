import TwoSidedLimitHomeomorph

namespace BoundaryOfSelf
namespace SummableTranslationWitness

noncomputable section

open Filter
open Set
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open ControlledEquivComposition
open FiniteControlledChain
open UniformCauchyLimitCarrier
open TwoSidedLimitHomeomorph


def translationControlled (shift : Real) : ControlledEquiv Real Real where
  toHomeomorph := Homeomorph.addRight shift
  forwardConstant := 1
  inverseConstant := 1
  forward_lipschitz := (isometry_add_right shift).lipschitz
  inverse_lipschitz := by
    have hInverse : ((Homeomorph.addRight shift).symm : Real -> Real) =
        fun point => point + (-shift) := by
      funext point
      change point - shift = point + (-shift)
      ring
    rw [hInverse]
    exact (isometry_add_right (-shift)).lipschitz

def targetShift (n : Nat) : Real := 1 - (1 / 2 : Real) ^ n

def translationIncrement (n : Nat) : Real := targetShift (n + 1) - targetShift n

def translationSequence (n : Nat) : ControlledEquiv Real Real :=
  translationControlled (translationIncrement n)

@[simp]
theorem targetShift_zero : targetShift 0 = 0 := by
  simp [targetShift]

theorem targetShift_tendsto_one : Tendsto targetShift atTop (nhds 1) := by
  have hPow : Tendsto (fun n : Nat => (1 / 2 : Real) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  change Tendsto (fun n : Nat => 1 - (1 / 2 : Real) ^ n) atTop (nhds 1)
  simpa only [sub_zero] using hPow.const_sub 1

theorem prefix_translation_apply (n : Nat) (point : Real) :
    prefixControlledEquiv translationSequence n point = point + targetShift n := by
  induction n with
  | zero => simp [prefixControlledEquiv]
  | succ n inductionHypothesis =>
      simp [prefixControlledEquiv, translationSequence, translationControlled,
        translationIncrement, inductionHypothesis]

theorem prefix_translation_inverse_apply (n : Nat) (point : Real) :
    (prefixControlledEquiv translationSequence n).toHomeomorph.symm point =
      point - targetShift n := by
  have hApply :=
    (prefixControlledEquiv translationSequence n).toHomeomorph.apply_symm_apply point
  rw [prefix_translation_apply] at hApply
  linarith

theorem prefix_translation_forwardConstant (n : Nat) :
    (prefixControlledEquiv translationSequence n).forwardConstant = 1 := by
  rw [prefixControlledEquiv_forwardConstant]
  simp [prefixForwardProduct, translationSequence, translationControlled]

theorem prefix_translation_inverseConstant (n : Nat) :
    (prefixControlledEquiv translationSequence n).inverseConstant = 1 := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simp [prefixControlledEquiv, translationSequence, translationControlled,
        composeControlled, inductionHypothesis]

theorem prefix_translations_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point => prefixControlledEquiv translationSequence n point)
      (fun point : Real => point + 1) atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hShift := targetShift_tendsto_one
  rw [Metric.tendsto_atTop] at hShift
  obtain ⟨N, hN⟩ := hShift epsilon hEpsilon
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  rw [prefix_translation_apply]
  calc
    dist (point + 1) (point + targetShift n) = dist 1 (targetShift n) := by
      exact dist_add_left point 1 (targetShift n)
    _ = dist (targetShift n) 1 := dist_comm _ _
    _ < epsilon := hN n hn

theorem inverse_prefix_translations_tendsto_uniformly :
    TendstoUniformlyOn
      (fun n point =>
        (prefixControlledEquiv translationSequence n).toHomeomorph.symm point)
      (fun point : Real => point - 1) atTop univ := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hEpsilon
  have hShift := targetShift_tendsto_one
  rw [Metric.tendsto_atTop] at hShift
  obtain ⟨N, hN⟩ := hShift epsilon hEpsilon
  refine eventually_atTop.2 ⟨N, fun n hn point _ => ?_⟩
  rw [prefix_translation_inverse_apply]
  calc
    dist (point - 1) (point - targetShift n) = dist 1 (targetShift n) := by
      rw [← dist_neg_neg]
      simp [sub_eq_add_neg, add_comm]
    _ = dist (targetShift n) 1 := dist_comm _ _
    _ < epsilon := hN n hn

theorem forward_prefixes_uniformCauchy :
    UniformCauchySeqOn
      (fun n point => prefixControlledEquiv translationSequence n point)
      atTop univ :=
  prefix_translations_tendsto_uniformly.uniformCauchySeqOn

theorem inverse_prefixes_uniformCauchy :
    UniformCauchySeqOn
      (fun n point =>
        (prefixControlledEquiv translationSequence n).toHomeomorph.symm point)
      atTop univ :=
  inverse_prefix_translations_tendsto_uniformly.uniformCauchySeqOn

theorem exists_unit_translation_limit
    (model : ComputableBoundaryModel Real) :
    ∃ limitHomeomorph : Real ≃ₜ Real,
      limitHomeomorph = Homeomorph.addRight 1 ∧
      frontier (limitHomeomorph '' model.inside) =
        limitHomeomorph '' model.interface ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          (prefixComputableBoundaryModel translationSequence n model).interface
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun n => Metric.hausdorffDist
          ((prefixComputableBoundaryModel translationSequence n model).approximation.carrier n)
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) := by
  obtain ⟨limitHomeomorph, hForwardLimit, _hInverseLimit,
    hFrontier, hMoving, hComputed⟩ :=
    exists_limit_homeomorph_and_actual_frontier
      translationSequence model forward_prefixes_uniformCauchy
      inverse_prefixes_uniformCauchy 1 1
      (fun n => by simp [prefix_translation_forwardConstant n])
      (fun n => by simp [prefix_translation_inverseConstant n])
  have hExact : limitHomeomorph = Homeomorph.addRight 1 := by
    ext point
    exact tendsto_nhds_unique
      (hForwardLimit.tendsto_at (mem_univ point))
      (prefix_translations_tendsto_uniformly.tendsto_at (mem_univ point))
  exact ⟨limitHomeomorph, hExact, hFrontier, hMoving, hComputed⟩

theorem unit_translation_is_nontrivial :
    (Homeomorph.addRight (1 : Real)) 0 = 1 := by
  norm_num

end
end SummableTranslationWitness
end BoundaryOfSelf
