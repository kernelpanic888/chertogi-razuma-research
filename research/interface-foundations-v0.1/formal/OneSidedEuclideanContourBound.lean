import LocalSegmentRealCompletion
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace BoundaryOfSelf
namespace OneSidedEuclideanContourBound

noncomputable section

open InterpolatedBoundaryContour
open LocalPolygonalContour
open LocalSegmentRadialBound
open LocalSegmentRealCompletion


def targetRadius : ℝ := Real.sqrt 2


def radialNorm (point : RealPlanePoint) : ℝ :=
  Real.sqrt (squaredRadius point)


def euclideanDistance (first second : RealPlanePoint) : ℝ :=
  Real.sqrt (squaredDistance first second)


def onTargetCircle (point : RealPlanePoint) : Prop :=
  squaredRadius point = 2


def radialCircleWitness (point : RealPlanePoint) : RealPlanePoint :=
  if squaredRadius point = 0 then
    { x := targetRadius, y := 0 }
  else
    { x := targetRadius * point.x / radialNorm point
      y := targetRadius * point.y / radialNorm point }


theorem squaredRadius_nonneg (point : RealPlanePoint) :
    0 ≤ squaredRadius point := by
  unfold squaredRadius
  positivity


theorem squaredDistance_nonneg (first second : RealPlanePoint) :
    0 ≤ squaredDistance first second := by
  unfold squaredDistance
  positivity


theorem targetRadius_nonneg : 0 ≤ targetRadius := by
  unfold targetRadius
  positivity


theorem targetRadius_pos : 0 < targetRadius := by
  unfold targetRadius
  positivity


theorem targetRadius_sq : targetRadius ^ 2 = 2 := by
  unfold targetRadius
  exact Real.sq_sqrt (by norm_num)


theorem radialNorm_nonneg (point : RealPlanePoint) :
    0 ≤ radialNorm point := by
  unfold radialNorm
  positivity


theorem radialNorm_sq (point : RealPlanePoint) :
    radialNorm point ^ 2 = squaredRadius point := by
  unfold radialNorm
  exact Real.sq_sqrt (squaredRadius_nonneg point)


theorem squaredRadius_eq_zero_iff (point : RealPlanePoint) :
    squaredRadius point = 0 ↔ point.x = 0 ∧ point.y = 0 := by
  unfold squaredRadius
  constructor
  · intro h
    have hx : point.x ^ 2 = 0 := by nlinarith [sq_nonneg point.x, sq_nonneg point.y]
    have hy : point.y ^ 2 = 0 := by nlinarith [sq_nonneg point.x, sq_nonneg point.y]
    constructor <;> nlinarith
  · rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num


theorem radialNorm_pos_of_radius_ne_zero (point : RealPlanePoint)
    (h : squaredRadius point ≠ 0) :
    0 < radialNorm point := by
  unfold radialNorm
  apply Real.sqrt_pos.2
  exact lt_of_le_of_ne (squaredRadius_nonneg point) (Ne.symm h)


theorem radialCircleWitness_on_circle (point : RealPlanePoint) :
    onTargetCircle (radialCircleWitness point) := by
  by_cases h : squaredRadius point = 0
  · rw [radialCircleWitness, if_pos h]
    unfold onTargetCircle squaredRadius
    dsimp
    simpa using targetRadius_sq
  · have hr := radialNorm_pos_of_radius_ne_zero point h
    have hrSq := radialNorm_sq point
    rw [radialCircleWitness, if_neg h]
    unfold onTargetCircle squaredRadius
    dsimp
    field_simp [ne_of_gt hr]
    change targetRadius ^ 2 * (point.x ^ 2 + point.y ^ 2) =
      radialNorm point ^ 2 * 2
    rw [targetRadius_sq]
    unfold squaredRadius at hrSq
    rw [hrSq]
    ring


theorem squaredDistance_scaled_self (point : RealPlanePoint) (scale : ℝ) :
    squaredDistance point { x := scale * point.x, y := scale * point.y } =
      (1 - scale) ^ 2 * squaredRadius point := by
  unfold squaredDistance squaredRadius
  ring


theorem squaredDistance_radialCircleWitness (point : RealPlanePoint) :
    squaredDistance point (radialCircleWitness point) =
      (targetRadius - radialNorm point) ^ 2 := by
  by_cases h : squaredRadius point = 0
  · have hxy := (squaredRadius_eq_zero_iff point).1 h
    rcases hxy with ⟨hx, hy⟩
    rw [radialCircleWitness, if_pos h]
    simp [squaredDistance, radialNorm, squaredRadius, hx, hy, targetRadius_sq]
  · have hr := radialNorm_pos_of_radius_ne_zero point h
    have hrSq := radialNorm_sq point
    have hScaled := squaredDistance_scaled_self point (targetRadius / radialNorm point)
    rw [radialCircleWitness, if_neg h]
    rw [show ({ x := targetRadius * point.x / radialNorm point,
                y := targetRadius * point.y / radialNorm point } : RealPlanePoint) =
          { x := (targetRadius / radialNorm point) * point.x,
            y := (targetRadius / radialNorm point) * point.y } by
      apply RealPlanePoint.ext <;> field_simp]
    rw [hScaled, ← hrSq]
    field_simp [ne_of_gt hr]
    ring


theorem radialNorm_le_targetRadius {point : RealPlanePoint}
    (hInside : squaredRadius point ≤ 2) :
    radialNorm point ≤ targetRadius := by
  unfold radialNorm targetRadius
  exact Real.sqrt_le_sqrt hInside


theorem euclideanDistance_radialCircleWitness {point : RealPlanePoint}
    (hInside : squaredRadius point ≤ 2) :
    euclideanDistance point (radialCircleWitness point) =
      targetRadius - radialNorm point := by
  rw [euclideanDistance, squaredDistance_radialCircleWitness]
  exact Real.sqrt_sq (sub_nonneg.mpr (radialNorm_le_targetRadius hInside))


theorem radial_distance_square_le_deficit {point : RealPlanePoint}
    (hInside : squaredRadius point ≤ 2) :
    (targetRadius - radialNorm point) ^ 2 ≤ 2 - squaredRadius point := by
  have hr0 := radialNorm_nonneg point
  have hrR := radialNorm_le_targetRadius hInside
  have hrSq := radialNorm_sq point
  have hRSq := targetRadius_sq
  have hProduct : 0 ≤ radialNorm point * (targetRadius - radialNorm point) :=
    mul_nonneg hr0 (sub_nonneg.mpr hrR)
  nlinarith


theorem euclideanDistance_to_circle_le_sqrt_deficit
    {point : RealPlanePoint} {bound : ℝ}
    (hDeficitNonneg : 0 ≤ 2 - squaredRadius point)
    (hDeficitBound : 2 - squaredRadius point ≤ bound) :
    euclideanDistance point (radialCircleWitness point) ≤ Real.sqrt bound := by
  have hInside : squaredRadius point ≤ 2 := by linarith
  have hBoundNonneg : 0 ≤ bound := le_trans hDeficitNonneg hDeficitBound
  have hDistanceNonneg : 0 ≤ targetRadius - radialNorm point :=
    sub_nonneg.mpr (radialNorm_le_targetRadius hInside)
  have hSquare := radial_distance_square_le_deficit hInside
  have hSqrtSq := Real.sq_sqrt hBoundNonneg
  have hSqrtNonneg := Real.sqrt_nonneg bound
  rw [euclideanDistance_radialCircleWitness hInside]
  nlinarith


def euclideanEnvelope (m : ℕ) : ℝ :=
  Real.sqrt 3 / (m : ℝ)


theorem sqrt_radial_bound_eq_euclideanEnvelope {m : ℕ} (hm : 0 < m) :
    Real.sqrt (3 * inverseCellSquare m) = euclideanEnvelope m := by
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hBoundNonneg : 0 ≤ 3 * inverseCellSquare m := by
    unfold inverseCellSquare
    positivity
  have hLeftSq := Real.sq_sqrt hBoundNonneg
  have hThreeSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hRightNonneg : 0 ≤ euclideanEnvelope m := by
    unfold euclideanEnvelope
    positivity
  have hRightSq : euclideanEnvelope m ^ 2 = 3 * inverseCellSquare m := by
    unfold euclideanEnvelope inverseCellSquare
    rw [div_pow, hThreeSq]
    ring
  have hLeftNonneg := Real.sqrt_nonneg (3 * inverseCellSquare m)
  nlinarith


def segmentRealPoint {m : ℕ} (t : ℝ)
    (segment : LocalContourSegment m)
    (firstVertex secondVertex : SegmentVertex segment) : RealPlanePoint :=
  let first := segmentEdge segment firstVertex
  let second := segmentEdge segment secondVertex
  realSegmentPoint t (firstRealEndpoint first second) (secondRealEndpoint first second)


def segmentCircleWitness {m : ℕ} (t : ℝ)
    (segment : LocalContourSegment m)
    (firstVertex secondVertex : SegmentVertex segment) : RealPlanePoint :=
  radialCircleWitness (segmentRealPoint t segment firstVertex secondVertex)


theorem local_segment_every_real_point_has_circle_witness {m : ℕ} (hm : 0 < m)
    (segment : LocalContourSegment m)
    (firstVertex secondVertex : SegmentVertex segment)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    onTargetCircle (segmentCircleWitness t segment firstVertex secondVertex) ∧
      euclideanDistance (segmentRealPoint t segment firstVertex secondVertex)
          (segmentCircleWitness t segment firstVertex secondVertex) ≤
        euclideanEnvelope m := by
  let first := segmentEdge segment firstVertex
  let second := segmentEdge segment secondVertex
  have hAll := local_segment_every_real_point_exact_and_bounded hm segment
    firstVertex secondVertex t ht0 ht1
  have hExact := hAll.1
  have hNonneg := hAll.2.1
  have hBound := hAll.2.2
  have hExact' :
      2 - squaredRadius (segmentRealPoint t segment firstVertex secondVertex) =
        realSegmentResidual t first second := by
    simpa [segmentRealPoint, first, second] using hExact
  constructor
  · exact radialCircleWitness_on_circle (segmentRealPoint t segment firstVertex secondVertex)
  · rw [← sqrt_radial_bound_eq_euclideanEnvelope hm]
    unfold segmentCircleWitness
    apply euclideanDistance_to_circle_le_sqrt_deficit
    · rw [hExact']
      exact hNonneg
    · rw [hExact']
      exact hBound


theorem one_sided_euclidean_epsilon
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, 0 < N ∧ ∀ (m : ℕ), N ≤ m →
      euclideanEnvelope m < epsilon := by
  obtain ⟨N, hNPos, hN⟩ := three_inverse_cell_square_epsilon
    (epsilon ^ 2) (sq_pos_of_pos hEpsilon)
  refine ⟨N, hNPos, ?_⟩
  intro m hm
  have hBound := hN m hm
  have hNonneg : 0 ≤ 3 * inverseCellSquare m := by
    unfold inverseCellSquare
    positivity
  have hSqrt := (Real.sqrt_lt hNonneg (le_of_lt hEpsilon)).2 hBound
  rw [sqrt_radial_bound_eq_euclideanEnvelope (lt_of_lt_of_le hNPos hm)] at hSqrt
  exact hSqrt

end
end OneSidedEuclideanContourBound
end BoundaryOfSelf
