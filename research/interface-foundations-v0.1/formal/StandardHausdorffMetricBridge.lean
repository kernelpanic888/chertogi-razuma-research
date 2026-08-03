import HausdorffStyleConvergence
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace BoundaryOfSelf
namespace StandardHausdorffMetricBridge

noncomputable section

open InterpolatedBoundaryContour
open LocalPolygonalContour
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open ReverseCoverageMetricAdapter
open ConcreteRadialContourTraversal
open DominantAxisReverseCoverage
open HausdorffStyleConvergence

/-!
IF-BS-22F-B3E embeds the authorial plane points into the canonical Euclidean
two-space and transports the audited pointwise witnesses to Mathlib's standard
`Metric.hausdorffDist`.
-/

abbrev AmbientPlane := EuclideanSpace Real (Fin 2)

def planeEmbedding (point : RealPlanePoint) : AmbientPlane :=
  !₂[point.x, point.y]

theorem planeEmbedding_injective : Function.Injective planeEmbedding := by
  intro first second h
  apply RealPlanePoint.ext
  · have h0 := congrFun (congrArg WithLp.ofLp h) 0
    simpa [planeEmbedding] using h0
  · have h1 := congrFun (congrArg WithLp.ofLp h) 1
    simpa [planeEmbedding] using h1

theorem dist_planeEmbedding_eq_euclideanDistance
    (first second : RealPlanePoint) :
    dist (planeEmbedding first) (planeEmbedding second) =
      euclideanDistance first second := by
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp [planeEmbedding, euclideanDistance, squaredDistance,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

def targetCircleCarrier : Set AmbientPlane :=
  {point | exists target : RealPlanePoint,
    onTargetCircle target /\ point = planeEmbedding target}

def contourCarrier (m : Nat) : Set AmbientPlane :=
  {point | exists (segment : LocalContourSegment m)
      (firstVertex secondVertex : SegmentVertex segment) (t : Real),
    0 <= t /\ t <= 1 /\
      point = planeEmbedding
        (segmentRealPoint t segment firstVertex secondVertex)}

def targetSeed : RealPlanePoint :=
  { x := targetRadius, y := 0 }

theorem targetSeed_onTargetCircle : onTargetCircle targetSeed := by
  unfold targetSeed onTargetCircle squaredRadius
  dsimp
  simpa using targetRadius_sq

theorem targetCircleCarrier_nonempty : targetCircleCarrier.Nonempty := by
  refine ⟨planeEmbedding targetSeed, ?_⟩
  exact ⟨targetSeed, targetSeed_onTargetCircle, rfl⟩

theorem contourCarrier_nonempty {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) : (contourCarrier m).Nonempty := by
  rcases target_has_contour_witness_four_div hm anchor targetSeed
      targetSeed_onTargetCircle with
    ⟨segment, firstVertex, secondVertex, t, ht0, ht1, _hDistance⟩
  refine ⟨planeEmbedding
    (segmentRealPoint t segment firstVertex secondVertex), ?_⟩
  exact ⟨segment, firstVertex, secondVertex, t, ht0, ht1, rfl⟩

theorem standard_hausdorffDist_le {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    Metric.hausdorffDist (contourCarrier m) targetCircleCarrier <=
      hausdorffEnvelope m := by
  have approximation := dominant_axis_hausdorff_style hm anchor
  apply Metric.hausdorffDist_le_of_mem_dist
  · unfold hausdorffEnvelope
    positivity
  · intro point hPoint
    rcases hPoint with
      ⟨segment, firstVertex, secondVertex, t, ht0, ht1, rfl⟩
    rcases approximation.contour_to_circle
        segment firstVertex secondVertex t ht0 ht1 with
      ⟨target, hTarget, hDistance⟩
    refine ⟨planeEmbedding target, ⟨target, hTarget, rfl⟩, ?_⟩
    rw [dist_planeEmbedding_eq_euclideanDistance]
    exact hDistance
  · intro point hPoint
    rcases hPoint with ⟨target, hTarget, rfl⟩
    rcases approximation.circle_to_contour.covers target hTarget with
      ⟨segment, firstVertex, secondVertex, t, ht0, ht1, hDistance⟩
    refine ⟨planeEmbedding
      (segmentRealPoint t segment firstVertex secondVertex),
      ⟨segment, firstVertex, secondVertex, t, ht0, ht1, rfl⟩, ?_⟩
    rw [dist_planeEmbedding_eq_euclideanDistance]
    exact hDistance

theorem standard_hausdorffDist_le_four_div {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    Metric.hausdorffDist (contourCarrier m) targetCircleCarrier <=
      4 / (m : Real) := by
  simpa [hausdorffEnvelope] using standard_hausdorffDist_le hm anchor

theorem standard_hausdorffDist_eventually_lt
    (epsilon : Real) (hEpsilon : 0 < epsilon) :
    exists N : Nat, 0 < N /\ forall m : Nat, N <= m ->
      forall _anchor : ContourState m,
        Metric.hausdorffDist (contourCarrier m) targetCircleCarrier < epsilon := by
  obtain ⟨N, hNPos, hN⟩ := hausdorffEnvelope_eventually_lt epsilon hEpsilon
  refine ⟨N, hNPos, ?_⟩
  intro m hm anchor
  have hmPos : 0 < m := lt_of_lt_of_le hNPos hm
  exact lt_of_le_of_lt (standard_hausdorffDist_le hmPos anchor) (hN m hm)

end
end StandardHausdorffMetricBridge
end BoundaryOfSelf

#print axioms BoundaryOfSelf.StandardHausdorffMetricBridge.dist_planeEmbedding_eq_euclideanDistance
#print axioms BoundaryOfSelf.StandardHausdorffMetricBridge.targetCircleCarrier_nonempty
#print axioms BoundaryOfSelf.StandardHausdorffMetricBridge.contourCarrier_nonempty
#print axioms BoundaryOfSelf.StandardHausdorffMetricBridge.standard_hausdorffDist_le
#print axioms BoundaryOfSelf.StandardHausdorffMetricBridge.standard_hausdorffDist_eventually_lt
