import FiniteControlledChain
import Mathlib.Topology.UniformSpace.UniformConvergence

namespace BoundaryOfSelf
namespace UniformCauchyLimitCarrier

noncomputable section

open Filter
open Set
open AbstractBoundaryApproximation
open BiLipschitzBoundaryTransport
open FiniteControlledChain

universe u

variable {X : Type u} [PseudoMetricSpace X]

/-!
IF-BS-22F-F6 closes the seam left by finite controlled chains. Uniform-Cauchy
prefix maps on the compact source interface have a uniform limit in a complete
ambient space. Their moving interface images converge in standard Hausdorff
distance to the single compact image of that limit. Under the F5 bounded-product
hypothesis, the moving computational carriers converge to the same carrier.
-/

theorem exists_uniform_limit_on
    [CompleteSpace X]
    (maps : Nat -> X -> X) (target : Set X)
    (hCauchy : UniformCauchySeqOn maps atTop target) :
    exists limitMap : X -> X, TendstoUniformlyOn maps limitMap atTop target := by
  classical
  choose pointLimit hPointLimit using fun point : target =>
    CompleteSpace.complete (hCauchy.cauchySeq point.property)
  let limitMap : X -> X := fun point =>
    if hPoint : point ∈ target then pointLimit ⟨point, hPoint⟩ else maps 0 point
  refine ⟨limitMap, hCauchy.tendstoUniformlyOn_of_tendsto ?_⟩
  intro point hPoint
  change map (fun n => maps n point) atTop ≤ nhds (limitMap point)
  simpa [limitMap, hPoint] using hPointLimit ⟨point, hPoint⟩

theorem hausdorffDist_images_le_of_pointwise_le
    (map limitMap : X -> X) (target : Set X) (error : Real)
    (hErrorNonnegative : 0 ≤ error)
    (hPointwise : ∀ point ∈ target, dist (limitMap point) (map point) ≤ error) :
    Metric.hausdorffDist (map '' target) (limitMap '' target) ≤ error := by
  refine Metric.hausdorffDist_le_of_mem_dist hErrorNonnegative ?_ ?_
  · intro mapped hMapped
    rcases hMapped with ⟨point, hPoint, rfl⟩
    refine ⟨limitMap point, ⟨point, hPoint, rfl⟩, ?_⟩
    simpa [dist_comm] using hPointwise point hPoint
  · intro limited hLimited
    rcases hLimited with ⟨point, hPoint, rfl⟩
    exact ⟨map point, ⟨point, hPoint, rfl⟩, hPointwise point hPoint⟩

theorem uniform_images_converge_in_hausdorff
    (maps : Nat -> X -> X) (limitMap : X -> X) (target : Set X)
    (hUniform : TendstoUniformlyOn maps limitMap atTop target) :
    Tendsto
      (fun n => Metric.hausdorffDist (maps n '' target) (limitMap '' target))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hEpsilon
  have hHalfPositive : 0 < epsilon / 2 := half_pos hEpsilon
  have hEventually :=
    (Metric.tendstoUniformlyOn_iff.mp hUniform) (epsilon / 2) hHalfPositive
  obtain ⟨N, hN⟩ := eventually_atTop.1 hEventually
  refine ⟨N, fun n hn => ?_⟩
  have hPointwise := hN n hn
  have hHausdorff :
      Metric.hausdorffDist (maps n '' target) (limitMap '' target) ≤ epsilon / 2 :=
    hausdorffDist_images_le_of_pointwise_le (maps n) limitMap target (epsilon / 2)
      (le_of_lt hHalfPositive) fun point hPoint => le_of_lt (hPointwise point hPoint)
  rw [Real.dist_eq]
  simpa only [sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg] using
    lt_of_le_of_lt hHausdorff (half_lt_self hEpsilon)

theorem uniform_limit_continuousOn
    (maps : Nat -> X -> X) (limitMap : X -> X) (target : Set X)
    (hUniform : TendstoUniformlyOn maps limitMap atTop target)
    (hContinuous : ∀ n, ContinuousOn (maps n) target) :
    ContinuousOn limitMap target := by
  exact hUniform.continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall hContinuous))

theorem uniform_limit_carrier_compact
    (maps : Nat -> X -> X) (limitMap : X -> X) (target : Set X)
    (hTargetCompact : IsCompact target)
    (hUniform : TendstoUniformlyOn maps limitMap atTop target)
    (hContinuous : ∀ n, ContinuousOn (maps n) target) :
    IsCompact (limitMap '' target) :=
  hTargetCompact.image_of_continuousOn
    (uniform_limit_continuousOn maps limitMap target hUniform hContinuous)

def PrefixUniformCauchy
    (sequence : Nat -> ControlledEquiv X X) (model : ComputableBoundaryModel X) : Prop :=
  UniformCauchySeqOn
    (fun depth point => prefixControlledEquiv sequence depth point)
    atTop model.interface

theorem prefix_interface_eq_image
    (sequence : Nat -> ControlledEquiv X X) (depth : Nat)
    (model : ComputableBoundaryModel X) :
    (prefixComputableBoundaryModel sequence depth model).interface =
      prefixControlledEquiv sequence depth '' model.interface := rfl

theorem exists_common_compact_limit_carrier
    [CompleteSpace X]
    (sequence : Nat -> ControlledEquiv X X) (model : ComputableBoundaryModel X)
    (hCauchy : PrefixUniformCauchy sequence model) :
    exists limitMap : X -> X, exists limitCarrier : Set X,
      TendstoUniformlyOn
        (fun depth point => prefixControlledEquiv sequence depth point)
        limitMap atTop model.interface ∧
      ContinuousOn limitMap model.interface ∧
      limitCarrier = limitMap '' model.interface ∧
      IsCompact limitCarrier ∧
      limitCarrier.Nonempty ∧
      Tendsto
        (fun depth => Metric.hausdorffDist
          (prefixComputableBoundaryModel sequence depth model).interface
          limitCarrier)
        atTop (nhds 0) := by
  obtain ⟨limitMap, hUniform⟩ := exists_uniform_limit_on
    (fun depth point => prefixControlledEquiv sequence depth point)
    model.interface hCauchy
  let limitCarrier : Set X := limitMap '' model.interface
  have hContinuous : ContinuousOn limitMap model.interface :=
    uniform_limit_continuousOn
      (fun depth point => prefixControlledEquiv sequence depth point)
      limitMap model.interface hUniform fun depth =>
        (prefixControlledEquiv sequence depth).toHomeomorph.continuous.continuousOn
  have hCompact : IsCompact limitCarrier := by
    exact model.approximation.target_compact.image_of_continuousOn hContinuous
  have hNonempty : limitCarrier.Nonempty := by
    exact model.approximation.target_nonempty.image limitMap
  have hMovingLimit :
      Tendsto
        (fun depth => Metric.hausdorffDist
          (prefixComputableBoundaryModel sequence depth model).interface
          limitCarrier)
        atTop (nhds 0) := by
    simpa only [prefix_interface_eq_image, limitCarrier] using
      uniform_images_converge_in_hausdorff
        (fun depth point => prefixControlledEquiv sequence depth point)
        limitMap model.interface hUniform
  exact ⟨limitMap, limitCarrier, hUniform, hContinuous, rfl,
    hCompact, hNonempty, hMovingLimit⟩

theorem computed_carriers_converge_to_common_limit
    (sequence : Nat -> ControlledEquiv X X) (model : ComputableBoundaryModel X)
    (limitCarrier : Set X)
    (hMovingLimit : Tendsto
      (fun depth => Metric.hausdorffDist
        (prefixComputableBoundaryModel sequence depth model).interface
        limitCarrier)
      atTop (nhds 0))
    (bound : Real)
    (hBound : ∀ depth, (prefixForwardProduct sequence depth : Real) ≤ bound) :
    Tendsto
      (fun depth => Metric.hausdorffDist
        ((prefixComputableBoundaryModel sequence depth model).approximation.carrier depth)
        limitCarrier)
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro depth
    exact Metric.hausdorffDist_nonneg
  · intro depth
    let prefixModel := prefixComputableBoundaryModel sequence depth model
    have hFinite : Metric.hausdorffEDist
        (prefixModel.approximation.carrier depth) prefixModel.interface ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (prefixModel.approximation.carrier_nonempty depth)
        prefixModel.approximation.target_nonempty
        (prefixModel.approximation.carrier_compact depth).isBounded
        prefixModel.approximation.target_compact.isBounded
    exact Metric.hausdorffDist_triangle hFinite
  · simpa using
      (bounded_prefix_moving_error_tendsto_zero sequence model bound hBound).add
        hMovingLimit

theorem exists_common_compact_limit_for_computed_carriers
    [CompleteSpace X]
    (sequence : Nat -> ControlledEquiv X X) (model : ComputableBoundaryModel X)
    (hCauchy : PrefixUniformCauchy sequence model)
    (bound : Real)
    (hBound : ∀ depth, (prefixForwardProduct sequence depth : Real) ≤ bound) :
    exists limitMap : X -> X, exists limitCarrier : Set X,
      TendstoUniformlyOn
        (fun depth point => prefixControlledEquiv sequence depth point)
        limitMap atTop model.interface ∧
      IsCompact limitCarrier ∧
      limitCarrier.Nonempty ∧
      Tendsto
        (fun depth => Metric.hausdorffDist
          ((prefixComputableBoundaryModel sequence depth model).approximation.carrier depth)
          limitCarrier)
        atTop (nhds 0) := by
  obtain ⟨limitMap, limitCarrier, hUniform, _hContinuous, _hCarrier,
    hCompact, hNonempty, hMovingLimit⟩ :=
    exists_common_compact_limit_carrier sequence model hCauchy
  exact ⟨limitMap, limitCarrier, hUniform, hCompact, hNonempty,
    computed_carriers_converge_to_common_limit
      sequence model limitCarrier hMovingLimit bound hBound⟩

end
end UniformCauchyLimitCarrier
end BoundaryOfSelf
