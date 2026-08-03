import StandardHausdorffMetricBridge
import Mathlib.Topology.MetricSpace.ProperSpace

namespace BoundaryOfSelf
namespace CompactHausdorffAttainment

noncomputable section

open Filter
open InterpolatedBoundaryContour
open LocalPolygonalContour
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open ReverseCoverageMetricAdapter
open ConcreteRadialContourTraversal
open HausdorffStyleConvergence
open StandardHausdorffMetricBridge

/-!
IF-BS-22F-B3F closes the topological packaging. The raw carriers are replaced
by their canonical closures, which preserve Hausdorff distance. Explicit ball
bounds make both closures compact; compactness then turns infimum bounds into
attained nearest-point witnesses. The standard Hausdorff distances are finally
packaged as an actual `Filter.Tendsto` statement.
-/

def closedTargetCarrier : Set AmbientPlane :=
  closure targetCircleCarrier

def closedContourCarrier (m : Nat) : Set AmbientPlane :=
  closure (contourCarrier m)

theorem norm_planeEmbedding_eq_radialNorm (point : RealPlanePoint) :
    ‖planeEmbedding point‖ = radialNorm point := by
  rw [EuclideanSpace.norm_eq]
  simp [planeEmbedding, radialNorm, squaredRadius,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem target_embedding_dist_zero {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    dist (planeEmbedding target) 0 = targetRadius := by
  rw [dist_zero_right, norm_planeEmbedding_eq_radialNorm]
  unfold radialNorm targetRadius
  rw [hTarget]

theorem targetCircleCarrier_subset_closedBall :
    targetCircleCarrier ⊆ Metric.closedBall 0 targetRadius := by
  intro point hPoint
  rcases hPoint with ⟨target, hTarget, rfl⟩
  rw [Metric.mem_closedBall, target_embedding_dist_zero hTarget]

theorem closedTargetCarrier_subset_closedBall :
    closedTargetCarrier ⊆ Metric.closedBall 0 targetRadius := by
  exact closure_minimal targetCircleCarrier_subset_closedBall
    Metric.isClosed_closedBall

theorem closedTargetCarrier_nonempty : closedTargetCarrier.Nonempty :=
  targetCircleCarrier_nonempty.closure

theorem closedTargetCarrier_compact : IsCompact closedTargetCarrier := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_closure,
    Metric.isBounded_closedBall.subset closedTargetCarrier_subset_closedBall⟩

theorem contourCarrier_subset_closedBall {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    contourCarrier m ⊆
      Metric.closedBall 0 (targetRadius + hausdorffEnvelope m) := by
  have approximation := dominant_axis_hausdorff_style hm anchor
  intro point hPoint
  rcases hPoint with
    ⟨segment, firstVertex, secondVertex, t, ht0, ht1, rfl⟩
  rcases approximation.contour_to_circle
      segment firstVertex secondVertex t ht0 ht1 with
    ⟨target, hTarget, hDistance⟩
  have hAmbientDistance :
      dist (planeEmbedding
          (segmentRealPoint t segment firstVertex secondVertex))
        (planeEmbedding target) <= hausdorffEnvelope m := by
    rw [dist_planeEmbedding_eq_euclideanDistance]
    exact hDistance
  rw [Metric.mem_closedBall]
  calc
    dist (planeEmbedding
        (segmentRealPoint t segment firstVertex secondVertex)) 0
        <= dist (planeEmbedding
              (segmentRealPoint t segment firstVertex secondVertex))
            (planeEmbedding target) + dist (planeEmbedding target) 0 :=
      dist_triangle _ _ _
    _ <= hausdorffEnvelope m + targetRadius :=
      add_le_add hAmbientDistance
        (le_of_eq (target_embedding_dist_zero hTarget))
    _ = targetRadius + hausdorffEnvelope m := by ring

theorem closedContourCarrier_subset_closedBall {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    closedContourCarrier m ⊆
      Metric.closedBall 0 (targetRadius + hausdorffEnvelope m) := by
  exact closure_minimal (contourCarrier_subset_closedBall hm anchor)
    Metric.isClosed_closedBall

theorem closedContourCarrier_nonempty {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) : (closedContourCarrier m).Nonempty :=
  (contourCarrier_nonempty hm anchor).closure

theorem closedContourCarrier_compact {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) : IsCompact (closedContourCarrier m) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_closure,
    Metric.isBounded_closedBall.subset
      (closedContourCarrier_subset_closedBall hm anchor)⟩

theorem closed_carriers_hausdorffDist_eq {m : Nat} :
    Metric.hausdorffDist (closedContourCarrier m) closedTargetCarrier =
      Metric.hausdorffDist (contourCarrier m) targetCircleCarrier := by
  exact Metric.hausdorffDist_closure

theorem closed_carriers_hausdorffDist_le {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    Metric.hausdorffDist (closedContourCarrier m) closedTargetCarrier <=
      hausdorffEnvelope m := by
  rw [closed_carriers_hausdorffDist_eq]
  exact standard_hausdorffDist_le hm anchor

theorem compact_hausdorffDist_le_iff_witnesses
    {firstSet secondSet : Set AmbientPlane} {radius : Real}
    (hFirstCompact : IsCompact firstSet)
    (hSecondCompact : IsCompact secondSet)
    (hFirstNonempty : firstSet.Nonempty)
    (hSecondNonempty : secondSet.Nonempty)
    (hRadius : 0 <= radius) :
    Metric.hausdorffDist firstSet secondSet <= radius ↔
      (∀ first ∈ firstSet, ∃ second ∈ secondSet,
        dist first second <= radius) /\
      (∀ second ∈ secondSet, ∃ first ∈ firstSet,
        dist second first <= radius) := by
  constructor
  · intro hHausdorff
    have hFiniteForward :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        hFirstNonempty hSecondNonempty
        hFirstCompact.isBounded hSecondCompact.isBounded
    have hFiniteReverse :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        hSecondNonempty hFirstNonempty
        hSecondCompact.isBounded hFirstCompact.isBounded
    constructor
    · intro first hFirst
      rcases hSecondCompact.exists_infDist_eq_dist
          hSecondNonempty first with
        ⟨second, hSecond, hNearest⟩
      refine ⟨second, hSecond, ?_⟩
      calc
        dist first second = Metric.infDist first secondSet := hNearest.symm
        _ <= Metric.hausdorffDist firstSet secondSet :=
          Metric.infDist_le_hausdorffDist_of_mem hFirst hFiniteForward
        _ <= radius := hHausdorff
    · intro second hSecond
      rcases hFirstCompact.exists_infDist_eq_dist
          hFirstNonempty second with
        ⟨first, hFirst, hNearest⟩
      refine ⟨first, hFirst, ?_⟩
      calc
        dist second first = Metric.infDist second firstSet := hNearest.symm
        _ <= Metric.hausdorffDist secondSet firstSet :=
          Metric.infDist_le_hausdorffDist_of_mem hSecond hFiniteReverse
        _ = Metric.hausdorffDist firstSet secondSet :=
          Metric.hausdorffDist_comm
        _ <= radius := hHausdorff
  · rintro ⟨hForward, hReverse⟩
    exact Metric.hausdorffDist_le_of_mem_dist hRadius hForward hReverse

theorem closed_carriers_hausdorffDist_le_iff_witnesses
    {m : Nat} (hm : 0 < m) (anchor : ContourState m)
    {radius : Real} (hRadius : 0 <= radius) :
    Metric.hausdorffDist (closedContourCarrier m) closedTargetCarrier <= radius ↔
      (∀ first ∈ closedContourCarrier m,
        ∃ second ∈ closedTargetCarrier, dist first second <= radius) /\
      (∀ second ∈ closedTargetCarrier,
        ∃ first ∈ closedContourCarrier m, dist second first <= radius) :=
  compact_hausdorffDist_le_iff_witnesses
    (closedContourCarrier_compact hm anchor)
    closedTargetCarrier_compact
    (closedContourCarrier_nonempty hm anchor)
    closedTargetCarrier_nonempty hRadius

def standardHausdorffSequence (n : Nat) : Real :=
  Metric.hausdorffDist (closedContourCarrier (n + 1)) closedTargetCarrier

theorem standardHausdorffSequence_tendsto_zero
    (_anchors : forall n : Nat, ContourState (n + 1)) :
    Tendsto standardHausdorffSequence atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hEpsilon
  obtain ⟨N, _hNPos, hN⟩ :=
    hausdorffEnvelope_eventually_lt epsilon hEpsilon
  refine ⟨N, ?_⟩
  intro n hn
  have hResolution : N <= n + 1 := le_trans hn (Nat.le_succ n)
  have hUpper : standardHausdorffSequence n < epsilon :=
    lt_of_le_of_lt
      (closed_carriers_hausdorffDist_le (Nat.succ_pos n) (_anchors n))
      (hN (n + 1) hResolution)
  have hNonnegative : 0 <= standardHausdorffSequence n :=
    Metric.hausdorffDist_nonneg
  simpa [Real.dist_eq, abs_of_nonneg hNonnegative] using hUpper

end
end CompactHausdorffAttainment
end BoundaryOfSelf

#print axioms BoundaryOfSelf.CompactHausdorffAttainment.closedTargetCarrier_compact
#print axioms BoundaryOfSelf.CompactHausdorffAttainment.closedContourCarrier_compact
#print axioms BoundaryOfSelf.CompactHausdorffAttainment.compact_hausdorffDist_le_iff_witnesses
#print axioms BoundaryOfSelf.CompactHausdorffAttainment.closed_carriers_hausdorffDist_le_iff_witnesses
#print axioms BoundaryOfSelf.CompactHausdorffAttainment.standardHausdorffSequence_tendsto_zero
