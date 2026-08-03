import UniformCauchyLimitCarrier

namespace BoundaryOfSelf
namespace TwoSidedLimitHomeomorph

noncomputable section

open Filter
open Set
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open FiniteControlledChain
open UniformCauchyLimitCarrier

universe u

variable {X : Type u} [MetricSpace X]

/-!
IF-BS-22F-F7 upgrades the F6 compact limit carrier to an actual transported
frontier. Both prefix maps and their inverses are uniformly Cauchy on the whole
ambient space. Uniform forward and inverse Lipschitz bounds let us pass the
moving inverse identities to the limit, producing a genuine limit homeomorphism.
-/

theorem moving_composition_tendsto
    (maps inverseMaps : Nat -> X -> X)
    (limitMap inverseLimit : X -> X)
    (hMaps : TendstoUniformlyOn maps limitMap atTop univ)
    (hInverseMaps : TendstoUniformlyOn inverseMaps inverseLimit atTop univ)
    (bound : Real) (hBoundNonnegative : 0 ≤ bound)
    (hLipschitz : ∀ n point other,
      dist (maps n point) (maps n other) ≤ bound * dist point other)
    (point : X) :
    Tendsto (fun n => maps n (inverseMaps n point)) atTop
      (nhds (limitMap (inverseLimit point))) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hEpsilon
  have hBoundPlusOne : 0 < bound + 1 := by linarith
  let delta : Real := epsilon / (2 * (bound + 1))
  have hDelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hHalf : 0 < epsilon / 2 := half_pos hEpsilon
  have hInverseEventually :=
    (Metric.tendstoUniformlyOn_iff.mp hInverseMaps) delta hDelta
  have hMapEventually :=
    (Metric.tendstoUniformlyOn_iff.mp hMaps) (epsilon / 2) hHalf
  obtain ⟨inverseN, hInverseN⟩ := eventually_atTop.1 hInverseEventually
  obtain ⟨mapN, hMapN⟩ := eventually_atTop.1 hMapEventually
  refine ⟨max inverseN mapN, fun n hn => ?_⟩
  have hInversePoint := hInverseN n (le_trans (le_max_left _ _) hn)
    point (mem_univ point)
  have hMapPoint := hMapN n (le_trans (le_max_right _ _) hn)
    (inverseLimit point) (mem_univ (inverseLimit point))
  have hRatio : bound / (bound + 1) < 1 :=
    (div_lt_one hBoundPlusOne).2 (by linarith)
  have hBoundDelta : bound * delta < epsilon / 2 := by
    calc
      bound * delta = (bound / (bound + 1)) * (epsilon / 2) := by
        dsimp [delta]
        field_simp [ne_of_gt hBoundPlusOne]
      _ < 1 * (epsilon / 2) := mul_lt_mul_of_pos_right hRatio hHalf
      _ = epsilon / 2 := one_mul _
  have hFirst :
      dist (maps n (inverseMaps n point)) (maps n (inverseLimit point)) <
        epsilon / 2 := by
    calc
      dist (maps n (inverseMaps n point)) (maps n (inverseLimit point)) ≤
          bound * dist (inverseMaps n point) (inverseLimit point) :=
        hLipschitz n (inverseMaps n point) (inverseLimit point)
      _ ≤ bound * delta := mul_le_mul_of_nonneg_left
        (le_of_lt (by simpa [dist_comm] using hInversePoint)) hBoundNonnegative
      _ < epsilon / 2 := hBoundDelta
  have hSecond :
      dist (maps n (inverseLimit point)) (limitMap (inverseLimit point)) <
        epsilon / 2 := by
    simpa [dist_comm] using hMapPoint
  calc
    dist (maps n (inverseMaps n point)) (limitMap (inverseLimit point)) ≤
        dist (maps n (inverseMaps n point)) (maps n (inverseLimit point)) +
          dist (maps n (inverseLimit point)) (limitMap (inverseLimit point)) :=
      dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add hFirst hSecond
    _ = epsilon := by ring

theorem exists_limit_homeomorph
    [CompleteSpace X]
    (sequence : Nat -> ControlledEquiv X X)
    (hForwardCauchy : UniformCauchySeqOn
      (fun depth point => prefixControlledEquiv sequence depth point) atTop univ)
    (hInverseCauchy : UniformCauchySeqOn
      (fun depth point =>
        (prefixControlledEquiv sequence depth).toHomeomorph.symm point) atTop univ)
    (forwardBound inverseBound : Real)
    (hForwardBound : ∀ depth,
      ((prefixControlledEquiv sequence depth).forwardConstant : Real) ≤ forwardBound)
    (hInverseBound : ∀ depth,
      ((prefixControlledEquiv sequence depth).inverseConstant : Real) ≤ inverseBound) :
    ∃ limitHomeomorph : X ≃ₜ X,
      TendstoUniformlyOn
        (fun depth point => prefixControlledEquiv sequence depth point)
        limitHomeomorph atTop univ ∧
      TendstoUniformlyOn
        (fun depth point =>
          (prefixControlledEquiv sequence depth).toHomeomorph.symm point)
        limitHomeomorph.symm atTop univ := by
  let forwardMaps : Nat -> X -> X :=
    fun depth point => prefixControlledEquiv sequence depth point
  let inverseMaps : Nat -> X -> X :=
    fun depth point => (prefixControlledEquiv sequence depth).toHomeomorph.symm point
  obtain ⟨limitMap, hLimitMap⟩ :=
    exists_uniform_limit_on forwardMaps univ hForwardCauchy
  obtain ⟨inverseLimit, hInverseLimit⟩ :=
    exists_uniform_limit_on inverseMaps univ hInverseCauchy
  have hForwardNonnegative : 0 ≤ forwardBound :=
    le_trans (NNReal.coe_nonneg _) (hForwardBound 0)
  have hInverseNonnegative : 0 ≤ inverseBound :=
    le_trans (NNReal.coe_nonneg _) (hInverseBound 0)
  have hForwardLipschitz : ∀ n point other,
      dist (forwardMaps n point) (forwardMaps n other) ≤
        forwardBound * dist point other := by
    intro n point other
    calc
      dist (forwardMaps n point) (forwardMaps n other) ≤
          ((prefixControlledEquiv sequence n).forwardConstant : Real) *
            dist point other :=
        (prefixControlledEquiv sequence n).forward_lipschitz.dist_le_mul point other
      _ ≤ forwardBound * dist point other :=
        mul_le_mul_of_nonneg_right (hForwardBound n) dist_nonneg
  have hInverseLipschitz : ∀ n point other,
      dist (inverseMaps n point) (inverseMaps n other) ≤
        inverseBound * dist point other := by
    intro n point other
    calc
      dist (inverseMaps n point) (inverseMaps n other) ≤
          ((prefixControlledEquiv sequence n).inverseConstant : Real) *
            dist point other :=
        (prefixControlledEquiv sequence n).inverse_lipschitz.dist_le_mul point other
      _ ≤ inverseBound * dist point other :=
        mul_le_mul_of_nonneg_right (hInverseBound n) dist_nonneg
  have hLeftInverse : Function.LeftInverse inverseLimit limitMap := by
    intro point
    have hTendsto := moving_composition_tendsto inverseMaps forwardMaps
      inverseLimit limitMap hInverseLimit hLimitMap inverseBound
      hInverseNonnegative hInverseLipschitz point
    have hExact : (fun n => inverseMaps n (forwardMaps n point)) =
        (fun _ : Nat => point) := by
      funext n
      exact (prefixControlledEquiv sequence n).toHomeomorph.symm_apply_apply point
    have hConstantToLimit : Tendsto (fun _ : Nat => point) atTop
        (nhds (inverseLimit (limitMap point))) := by
      simpa only [hExact] using hTendsto
    exact tendsto_nhds_unique hConstantToLimit tendsto_const_nhds
  have hRightInverse : Function.RightInverse inverseLimit limitMap := by
    intro point
    have hTendsto := moving_composition_tendsto forwardMaps inverseMaps
      limitMap inverseLimit hLimitMap hInverseLimit forwardBound
      hForwardNonnegative hForwardLipschitz point
    have hExact : (fun n => forwardMaps n (inverseMaps n point)) =
        (fun _ : Nat => point) := by
      funext n
      exact (prefixControlledEquiv sequence n).toHomeomorph.apply_symm_apply point
    have hConstantToLimit : Tendsto (fun _ : Nat => point) atTop
        (nhds (limitMap (inverseLimit point))) := by
      simpa only [hExact] using hTendsto
    exact tendsto_nhds_unique hConstantToLimit tendsto_const_nhds
  have hLimitContinuous : Continuous limitMap := by
    have hOn : ContinuousOn limitMap univ :=
      uniform_limit_continuousOn forwardMaps limitMap univ hLimitMap fun n =>
        (prefixControlledEquiv sequence n).toHomeomorph.continuous.continuousOn
    simpa only [continuousOn_univ] using hOn
  have hInverseContinuous : Continuous inverseLimit := by
    have hOn : ContinuousOn inverseLimit univ :=
      uniform_limit_continuousOn inverseMaps inverseLimit univ hInverseLimit fun n =>
        (prefixControlledEquiv sequence n).toHomeomorph.symm.continuous.continuousOn
    simpa only [continuousOn_univ] using hOn
  let limitEquiv : X ≃ X :=
    { toFun := limitMap
      invFun := inverseLimit
      left_inv := hLeftInverse
      right_inv := hRightInverse }
  let limitHomeomorph : X ≃ₜ X :=
    Homeomorph.mk limitEquiv hLimitContinuous hInverseContinuous
  refine ⟨limitHomeomorph, ?_, ?_⟩
  · change TendstoUniformlyOn forwardMaps limitMap atTop univ
    exact hLimitMap
  · change TendstoUniformlyOn inverseMaps inverseLimit atTop univ
    exact hInverseLimit

theorem limit_interface_is_actual_frontier
    (limitHomeomorph : X ≃ₜ X) (model : ComputableBoundaryModel X) :
    frontier (limitHomeomorph '' model.inside) =
      limitHomeomorph '' model.interface := by
  rw [← limitHomeomorph.image_frontier]
  rw [model.interface_is_frontier]

theorem exists_limit_homeomorph_and_actual_frontier
    [CompleteSpace X]
    (sequence : Nat -> ControlledEquiv X X) (model : ComputableBoundaryModel X)
    (hForwardCauchy : UniformCauchySeqOn
      (fun depth point => prefixControlledEquiv sequence depth point) atTop univ)
    (hInverseCauchy : UniformCauchySeqOn
      (fun depth point =>
        (prefixControlledEquiv sequence depth).toHomeomorph.symm point) atTop univ)
    (forwardBound inverseBound : Real)
    (hForwardBound : ∀ depth,
      ((prefixControlledEquiv sequence depth).forwardConstant : Real) ≤ forwardBound)
    (hInverseBound : ∀ depth,
      ((prefixControlledEquiv sequence depth).inverseConstant : Real) ≤ inverseBound) :
    ∃ limitHomeomorph : X ≃ₜ X,
      TendstoUniformlyOn
        (fun depth point => prefixControlledEquiv sequence depth point)
        limitHomeomorph atTop univ ∧
      TendstoUniformlyOn
        (fun depth point =>
          (prefixControlledEquiv sequence depth).toHomeomorph.symm point)
        limitHomeomorph.symm atTop univ ∧
      frontier (limitHomeomorph '' model.inside) =
        limitHomeomorph '' model.interface ∧
      Tendsto
        (fun depth => Metric.hausdorffDist
          (prefixComputableBoundaryModel sequence depth model).interface
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) ∧
      Tendsto
        (fun depth => Metric.hausdorffDist
          ((prefixComputableBoundaryModel sequence depth model).approximation.carrier depth)
          (limitHomeomorph '' model.interface))
        atTop (nhds 0) := by
  obtain ⟨limitHomeomorph, hForwardLimit, hInverseLimit⟩ :=
    exists_limit_homeomorph sequence hForwardCauchy hInverseCauchy
      forwardBound inverseBound hForwardBound hInverseBound
  have hMovingLimit : Tendsto
      (fun depth => Metric.hausdorffDist
        (prefixComputableBoundaryModel sequence depth model).interface
        (limitHomeomorph '' model.interface))
      atTop (nhds 0) := by
    simpa only [prefix_interface_eq_image] using
      uniform_images_converge_in_hausdorff
        (fun depth point => prefixControlledEquiv sequence depth point)
        limitHomeomorph model.interface (hForwardLimit.mono (subset_univ _))
  have hProductBound : ∀ depth,
      (prefixForwardProduct sequence depth : Real) ≤ forwardBound := by
    intro depth
    rw [← prefixControlledEquiv_forwardConstant]
    exact hForwardBound depth
  exact ⟨limitHomeomorph, hForwardLimit, hInverseLimit,
    limit_interface_is_actual_frontier limitHomeomorph model,
    hMovingLimit,
    computed_carriers_converge_to_common_limit sequence model
      (limitHomeomorph '' model.interface) hMovingLimit forwardBound hProductBound⟩

end
end TwoSidedLimitHomeomorph
end BoundaryOfSelf
