import OneSidedEuclideanContourBound
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace BoundaryOfSelf
namespace ReverseCoverageMetricAdapter

noncomputable section

open LocalPolygonalContour
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound


def coordinateNorm (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2)


theorem coordinateNorm_nonneg (x y : ℝ) :
    0 ≤ coordinateNorm x y := by
  unfold coordinateNorm
  positivity


theorem coordinateNorm_sq (x y : ℝ) :
    coordinateNorm x y ^ 2 = x ^ 2 + y ^ 2 := by
  unfold coordinateNorm
  exact Real.sq_sqrt (by positivity)


theorem planar_cauchy_schwarz (a b c d : ℝ) :
    a * c + b * d ≤ coordinateNorm a b * coordinateNorm c d := by
  let A := coordinateNorm a b
  let B := coordinateNorm c d
  have hA0 : 0 ≤ A := coordinateNorm_nonneg a b
  have hB0 : 0 ≤ B := coordinateNorm_nonneg c d
  have hA2 : A ^ 2 = a ^ 2 + b ^ 2 := coordinateNorm_sq a b
  have hB2 : B ^ 2 = c ^ 2 + d ^ 2 := coordinateNorm_sq c d
  have hIdentity :
      (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 = A ^ 2 * B ^ 2 := by
    rw [hA2, hB2]
    ring
  have hDotSq : (a * c + b * d) ^ 2 ≤ (A * B) ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg (a * d - b * c)]
  by_cases hDot : a * c + b * d ≤ 0
  · exact le_trans hDot (mul_nonneg hA0 hB0)
  · exact (sq_le_sq₀ (le_of_not_ge hDot) (mul_nonneg hA0 hB0)).1 hDotSq


theorem coordinateNorm_triangle (a b c d : ℝ) :
    coordinateNorm (a + c) (b + d) ≤ coordinateNorm a b + coordinateNorm c d := by
  let A := coordinateNorm a b
  let B := coordinateNorm c d
  let C := coordinateNorm (a + c) (b + d)
  have hA0 : 0 ≤ A := coordinateNorm_nonneg a b
  have hB0 : 0 ≤ B := coordinateNorm_nonneg c d
  have hC0 : 0 ≤ C := coordinateNorm_nonneg (a + c) (b + d)
  have hA2 : A ^ 2 = a ^ 2 + b ^ 2 := coordinateNorm_sq a b
  have hB2 : B ^ 2 = c ^ 2 + d ^ 2 := coordinateNorm_sq c d
  have hC2 : C ^ 2 = (a + c) ^ 2 + (b + d) ^ 2 := coordinateNorm_sq (a + c) (b + d)
  have hDot := planar_cauchy_schwarz a b c d
  have hSquare : C ^ 2 ≤ (A + B) ^ 2 := by
    dsimp only [A, B, C] at *
    nlinarith
  exact (sq_le_sq₀ hC0 (add_nonneg hA0 hB0)).1 hSquare


theorem euclideanDistance_eq_coordinateNorm (first second : RealPlanePoint) :
    euclideanDistance first second =
      coordinateNorm (first.x - second.x) (first.y - second.y) := by
  rfl


theorem euclideanDistance_nonneg (first second : RealPlanePoint) :
    0 ≤ euclideanDistance first second := by
  unfold euclideanDistance
  positivity


theorem euclideanDistance_refl (point : RealPlanePoint) :
    euclideanDistance point point = 0 := by
  unfold euclideanDistance squaredDistance
  simp


theorem euclideanDistance_comm (first second : RealPlanePoint) :
    euclideanDistance first second = euclideanDistance second first := by
  unfold euclideanDistance squaredDistance
  congr 1
  ring


theorem euclideanDistance_triangle (first middle last : RealPlanePoint) :
    euclideanDistance first last ≤
      euclideanDistance first middle + euclideanDistance middle last := by
  rw [euclideanDistance_eq_coordinateNorm, euclideanDistance_eq_coordinateNorm,
    euclideanDistance_eq_coordinateNorm]
  have h := coordinateNorm_triangle
    (first.x - middle.x) (first.y - middle.y)
    (middle.x - last.x) (middle.y - last.y)
  convert h using 1
  all_goals ring_nf


structure ReverseCoverageMesh (m : ℕ) (meshWidth : ℝ) : Prop where
  covers : ∀ target : RealPlanePoint, onTargetCircle target →
    ∃ (segment : LocalContourSegment m)
      (firstVertex secondVertex : SegmentVertex segment)
      (t : ℝ),
      0 ≤ t ∧ t ≤ 1 ∧
      euclideanDistance target
        (segmentCircleWitness t segment firstVertex secondVertex) ≤ meshWidth


structure ReverseCoverageWitness (m : ℕ) (bound : ℝ) : Prop where
  covers : ∀ target : RealPlanePoint, onTargetCircle target →
    ∃ (segment : LocalContourSegment m)
      (firstVertex secondVertex : SegmentVertex segment)
      (t : ℝ),
      0 ≤ t ∧ t ≤ 1 ∧
      euclideanDistance target
        (segmentRealPoint t segment firstVertex secondVertex) ≤ bound


theorem reverseCoverage_of_mesh {m : ℕ} (hm : 0 < m)
    {meshWidth : ℝ} (mesh : ReverseCoverageMesh m meshWidth) :
    ReverseCoverageWitness m (meshWidth + euclideanEnvelope m) := by
  constructor
  intro target hTarget
  obtain ⟨segment, firstVertex, secondVertex, t, ht0, ht1, hMesh⟩ :=
    mesh.covers target hTarget
  have hRadial := local_segment_every_real_point_has_circle_witness hm segment
    firstVertex secondVertex t ht0 ht1
  refine ⟨segment, firstVertex, secondVertex, t, ht0, ht1, ?_⟩
  have hTriangle := euclideanDistance_triangle target
    (segmentCircleWitness t segment firstVertex secondVertex)
    (segmentRealPoint t segment firstVertex secondVertex)
  have hRadialSymm :
      euclideanDistance (segmentCircleWitness t segment firstVertex secondVertex)
          (segmentRealPoint t segment firstVertex secondVertex) ≤ euclideanEnvelope m := by
    rw [euclideanDistance_comm]
    exact hRadial.2
  exact le_trans hTriangle (add_le_add hMesh hRadialSymm)


structure BidirectionalCircleApproximation (m : ℕ)
    (forwardBound reverseBound : ℝ) : Prop where
  contour_to_circle : ∀
    (segment : LocalContourSegment m)
    (firstVertex secondVertex : SegmentVertex segment)
    (t : ℝ), 0 ≤ t → t ≤ 1 →
    ∃ target : RealPlanePoint,
      onTargetCircle target ∧
      euclideanDistance (segmentRealPoint t segment firstVertex secondVertex) target ≤
        forwardBound
  circle_to_contour : ReverseCoverageWitness m reverseBound


theorem bidirectionalCircleApproximation_of_mesh {m : ℕ} (hm : 0 < m)
    {meshWidth : ℝ} (mesh : ReverseCoverageMesh m meshWidth) :
    BidirectionalCircleApproximation m (euclideanEnvelope m)
      (meshWidth + euclideanEnvelope m) := by
  constructor
  · intro segment firstVertex secondVertex t ht0 ht1
    refine ⟨segmentCircleWitness t segment firstVertex secondVertex, ?_⟩
    exact local_segment_every_real_point_has_circle_witness hm segment
      firstVertex secondVertex t ht0 ht1
  · exact reverseCoverage_of_mesh hm mesh

end
end ReverseCoverageMetricAdapter
end BoundaryOfSelf
