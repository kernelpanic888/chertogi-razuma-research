import DominantBranchCoordinateBound

namespace BoundaryOfSelf
namespace DominantAxisReverseCoverage

noncomputable section

open InterpolatedBoundaryContour
open LocalPolygonalContour
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open ReverseCoverageMetricAdapter
open ConcreteRadialContourTraversal
open CircleAxisRounding
open OrbitCrossingLocalSegment
open DominantAxisLocalSegment
open CrossingInterpolationPhysicalBridge
open DominantBranchCoordinateBound

/-!
IF-BS-22F-B3C2C closes reverse coverage. Every target-circle point selects a
pole-stable crossing on the unique global orbit, extracts its local segment,
and uses that crossing endpoint at t=0 as a contour witness within 4/m.
-/

theorem target_has_contour_witness_four_div {m : Nat} (hm : 0 < m)
    (anchor : ContourState m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target) :
    exists (segment : LocalContourSegment m)
      (firstVertex secondVertex : SegmentVertex segment) (t : Real),
      0 <= t /\ t <= 1 /\
      euclideanDistance target
        (segmentRealPoint t segment firstVertex secondVertex) <= 4 / (m : Real) := by
  rcases target_has_dominant_local_segment_on_global_orbit hm anchor target hTarget with
    ⟨horizontal, vertical, ⟨witness⟩⟩
  let segment := localSegmentOfState witness.state
  let vertex := segmentVertexOfState witness.state
  let edge := segmentEdgeOfState witness.state
  refine ⟨segment, vertex, vertex, 0, le_rfl, zero_le_one, ?_⟩
  rw [segmentRealPoint_zero_self_eq_physical hm]
  change euclideanDistance target (edgePhysicalInterpolation edge) <= 4 / (m : Real)
  by_cases hDominant : |target.y| <= |target.x|
  · by_cases hSign : 0 <= target.x
    · have hInner : innerPoint edge = horizontal.right.insidePoint := by
        simpa [edge, dominantFacingCrossing, hDominant,
          signFacingCrossing, hSign] using witness.inner_eq
      have hOuter : outerPoint edge = horizontal.right.outsidePoint := by
        simpa [edge, dominantFacingCrossing, hDominant,
          signFacingCrossing, hSign] using witness.outer_eq
      have hBounds := right_edge_coordinate_bounds hm target hTarget horizontal
        edge hInner hOuter hDominant hSign
      exact euclideanDistance_le_four_div hm target
        (edgePhysicalInterpolation edge) hBounds.1 hBounds.2
    · have hNegative : target.x < 0 := lt_of_not_ge hSign
      have hInner : innerPoint edge = horizontal.left.insidePoint := by
        simpa [edge, dominantFacingCrossing, hDominant,
          signFacingCrossing, hSign] using witness.inner_eq
      have hOuter : outerPoint edge = horizontal.left.outsidePoint := by
        simpa [edge, dominantFacingCrossing, hDominant,
          signFacingCrossing, hSign] using witness.outer_eq
      have hBounds := left_edge_coordinate_bounds hm target hTarget horizontal
        edge hInner hOuter hDominant hNegative
      exact euclideanDistance_le_four_div hm target
        (edgePhysicalInterpolation edge) hBounds.1 hBounds.2
  · by_cases hSign : 0 <= target.y
    · have hInner : innerPoint edge = vertical.top.insidePoint := by
        simpa [edge, dominantFacingCrossing, hDominant,
          verticalFacingCrossing, hSign] using witness.inner_eq
      have hOuter : outerPoint edge = vertical.top.outsidePoint := by
        simpa [edge, dominantFacingCrossing, hDominant,
          verticalFacingCrossing, hSign] using witness.outer_eq
      have hBounds := top_edge_coordinate_bounds hm target hTarget vertical
        edge hInner hOuter hDominant hSign
      exact euclideanDistance_le_four_div_swapped hm target
        (edgePhysicalInterpolation edge) hBounds.1 hBounds.2
    · have hNegative : target.y < 0 := lt_of_not_ge hSign
      have hInner : innerPoint edge = vertical.bottom.insidePoint := by
        simpa [edge, dominantFacingCrossing, hDominant,
          verticalFacingCrossing, hSign] using witness.inner_eq
      have hOuter : outerPoint edge = vertical.bottom.outsidePoint := by
        simpa [edge, dominantFacingCrossing, hDominant,
          verticalFacingCrossing, hSign] using witness.outer_eq
      have hBounds := bottom_edge_coordinate_bounds hm target hTarget vertical
        edge hInner hOuter hDominant hNegative
      exact euclideanDistance_le_four_div_swapped hm target
        (edgePhysicalInterpolation edge) hBounds.1 hBounds.2

theorem dominant_axis_reverseCoverage {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    ReverseCoverageWitness m (4 / (m : Real)) where
  covers := by
    intro target hTarget
    exact target_has_contour_witness_four_div hm anchor target hTarget

theorem dominant_axis_bidirectional_approximation {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    BidirectionalCircleApproximation m (euclideanEnvelope m) (4 / (m : Real)) where
  contour_to_circle := by
    intro segment firstVertex secondVertex t ht0 ht1
    refine ⟨segmentCircleWitness t segment firstVertex secondVertex, ?_⟩
    exact local_segment_every_real_point_has_circle_witness hm segment
      firstVertex secondVertex t ht0 ht1
  circle_to_contour := dominant_axis_reverseCoverage hm anchor

end
end DominantAxisReverseCoverage
end BoundaryOfSelf

#print axioms BoundaryOfSelf.DominantAxisReverseCoverage.target_has_contour_witness_four_div
#print axioms BoundaryOfSelf.DominantAxisReverseCoverage.dominant_axis_reverseCoverage
#print axioms BoundaryOfSelf.DominantAxisReverseCoverage.dominant_axis_bidirectional_approximation
