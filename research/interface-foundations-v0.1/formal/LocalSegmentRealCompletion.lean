import LocalSegmentRadialBound
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace BoundaryOfSelf
namespace LocalSegmentRealCompletion

noncomputable section

open InterpolatedBoundaryContour
open InterpolatedSignedCoordinates
open LocalSegmentRadialBound

@[ext] structure RealPlanePoint where
  x : ℝ
  y : ℝ


def squaredRadius (point : RealPlanePoint) : ℝ :=
  point.x ^ 2 + point.y ^ 2


def squaredDistance (first second : RealPlanePoint) : ℝ :=
  (first.x - second.x) ^ 2 + (first.y - second.y) ^ 2


abbrev realCommonDenominator {m : ℕ}
    (first second : CrossingEdge m) : ℝ :=
  commonDenominator m first second


def firstRealEndpoint {m : ℕ}
    (first second : CrossingEdge m) : RealPlanePoint :=
  { x := commonCenteredXFirst first second / realCommonDenominator first second
    y := commonCenteredYFirst first second / realCommonDenominator first second }


def secondRealEndpoint {m : ℕ}
    (first second : CrossingEdge m) : RealPlanePoint :=
  { x := commonCenteredXSecond first second / realCommonDenominator first second
    y := commonCenteredYSecond first second / realCommonDenominator first second }


def firstRealResidual {m : ℕ}
    (first second : CrossingEdge m) : ℝ :=
  commonFirstResidual first second / (realCommonDenominator first second) ^ 2


def secondRealResidual {m : ℕ}
    (first second : CrossingEdge m) : ℝ :=
  commonSecondResidual first second / (realCommonDenominator first second) ^ 2


def inverseCellSquare (m : ℕ) : ℝ := 1 / (m : ℝ) ^ 2


theorem commonScale_pos {m : ℕ} (first second : CrossingEdge m) :
    0 < commonScale first second := by
  exact Nat.mul_pos (interpolationDenominator_pos first) (interpolationDenominator_pos second)


theorem realCommonDenominator_pos {m : ℕ} (hm : 0 < m)
    (first second : CrossingEdge m) :
    0 < realCommonDenominator first second := by
  rw [realCommonDenominator]
  exact_mod_cast Nat.mul_pos (commonScale_pos first second) hm


theorem first_radius_deficit_exact {m : ℕ} (hm : 0 < m)
    (first second : CrossingEdge m) :
    2 - squaredRadius (firstRealEndpoint first second) =
      firstRealResidual first second := by
  have h := common_first_radius_identity hm first second
  have hR :
      (commonCenteredXFirst first second : ℝ) * commonCenteredXFirst first second +
          (commonCenteredYFirst first second : ℝ) * commonCenteredYFirst first second +
          (commonFirstResidual first second : ℝ) =
        2 * (commonDenominator m first second : ℝ) *
          (commonDenominator m first second : ℝ) := by
    exact_mod_cast h
  have hD := realCommonDenominator_pos hm first second
  rw [firstRealResidual, firstRealEndpoint, squaredRadius]
  dsimp
  rw [div_pow, div_pow]
  field_simp [realCommonDenominator, ne_of_gt hD]
  nlinarith


theorem second_radius_deficit_exact {m : ℕ} (hm : 0 < m)
    (first second : CrossingEdge m) :
    2 - squaredRadius (secondRealEndpoint first second) =
      secondRealResidual first second := by
  have h := common_second_radius_identity hm first second
  have hR :
      (commonCenteredXSecond first second : ℝ) * commonCenteredXSecond first second +
          (commonCenteredYSecond first second : ℝ) * commonCenteredYSecond first second +
          (commonSecondResidual first second : ℝ) =
        2 * (commonDenominator m first second : ℝ) *
          (commonDenominator m first second : ℝ) := by
    exact_mod_cast h
  have hD := realCommonDenominator_pos hm first second
  rw [secondRealResidual, secondRealEndpoint, squaredRadius]
  dsimp
  rw [div_pow, div_pow]
  field_simp [realCommonDenominator, ne_of_gt hD]
  nlinarith


theorem firstRealResidual_nonneg {m : ℕ} (hm : 0 < m)
    (first second : CrossingEdge m) :
    0 ≤ firstRealResidual first second := by
  unfold firstRealResidual
  positivity


theorem secondRealResidual_nonneg {m : ℕ} (hm : 0 < m)
    (first second : CrossingEdge m) :
    0 ≤ secondRealResidual first second := by
  unfold secondRealResidual
  positivity


theorem firstRealResidual_le {m : ℕ} (hm : 0 < m)
    (first second : CrossingEdge m) :
    firstRealResidual first second ≤ inverseCellSquare m := by
  have hNat := commonFirstResidual_le_scaleSquare first second
  have hCast : (commonFirstResidual first second : ℝ) ≤
      (commonScale first second : ℝ) * commonScale first second := by
    exact_mod_cast hNat
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  have hD := realCommonDenominator_pos hm first second
  apply (div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos hM)).2
  have hScaled := mul_le_mul_of_nonneg_right hCast (sq_nonneg (m : ℝ))
  change (commonFirstResidual first second : ℝ) * (m : ℝ) ^ 2 ≤
    1 * (commonDenominator m first second : ℝ) ^ 2
  simp only [one_mul, commonDenominator, Nat.cast_mul]
  convert hScaled using 1 <;> ring


theorem secondRealResidual_le {m : ℕ} (hm : 0 < m)
    (first second : CrossingEdge m) :
    secondRealResidual first second ≤ inverseCellSquare m := by
  have hNat := commonSecondResidual_le_scaleSquare first second
  have hCast : (commonSecondResidual first second : ℝ) ≤
      (commonScale first second : ℝ) * commonScale first second := by
    exact_mod_cast hNat
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  have hD := realCommonDenominator_pos hm first second
  apply (div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos hM)).2
  have hScaled := mul_le_mul_of_nonneg_right hCast (sq_nonneg (m : ℝ))
  change (commonSecondResidual first second : ℝ) * (m : ℝ) ^ 2 ≤
    1 * (commonDenominator m first second : ℝ) ^ 2
  simp only [one_mul, commonDenominator, Nat.cast_mul]
  convert hScaled using 1 <;> ring


theorem endpoint_squaredDistance_exact {m : ℕ} (hm : 0 < m)
    (first second : CrossingEdge m) :
    squaredDistance (firstRealEndpoint first second) (secondRealEndpoint first second) =
      (commonSquaredSeparation first second : ℝ) /
        (realCommonDenominator first second) ^ 2 := by
  have h := common_centered_separation_exact first second
  have hR :
      ((commonCenteredXFirst first second - commonCenteredXSecond first second : ℤ) : ℝ) *
          ((commonCenteredXFirst first second - commonCenteredXSecond first second : ℤ) : ℝ) +
        ((commonCenteredYFirst first second - commonCenteredYSecond first second : ℤ) : ℝ) *
          ((commonCenteredYFirst first second - commonCenteredYSecond first second : ℤ) : ℝ) =
        (commonSquaredSeparation first second : ℝ) := by
    exact_mod_cast h
  have hD := realCommonDenominator_pos hm first second
  rw [squaredDistance, firstRealEndpoint, secondRealEndpoint]
  dsimp
  field_simp [realCommonDenominator, ne_of_gt hD]
  push_cast at hR
  nlinarith


theorem endpoint_squaredDistance_le {m : ℕ} (hm : 0 < m)
    (cell : LocalPolygonalContour.GridCell m)
    (firstSide secondSide : LocalPolygonalContour.CellSide)
    (firstCrossing : firstSide ∈ LocalPolygonalContour.crossingSides cell)
    (secondCrossing : secondSide ∈ LocalPolygonalContour.crossingSides cell) :
    let first := LocalPolygonalContour.crossingEdgeForSide cell firstSide firstCrossing
    let second := LocalPolygonalContour.crossingEdgeForSide cell secondSide secondCrossing
    squaredDistance (firstRealEndpoint first second) (secondRealEndpoint first second) ≤
      2 * inverseCellSquare m := by
  dsimp only
  let first := LocalPolygonalContour.crossingEdgeForSide cell firstSide firstCrossing
  let second := LocalPolygonalContour.crossingEdgeForSide cell secondSide secondCrossing
  have hNat := same_cell_common_separation_le cell firstSide secondSide firstCrossing secondCrossing
  have hCast : (commonSquaredSeparation first second : ℝ) ≤
      2 * (commonScale first second : ℝ) * commonScale first second := by
    exact_mod_cast hNat
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  have hD := realCommonDenominator_pos hm first second
  rw [endpoint_squaredDistance_exact hm first second]
  rw [show 2 * inverseCellSquare m = 2 / (m : ℝ) ^ 2 by
    simp [inverseCellSquare, div_eq_mul_inv]]
  apply (div_le_div_iff₀ (sq_pos_of_pos hD) (sq_pos_of_pos hM)).2
  have hScaled := mul_le_mul_of_nonneg_right hCast (sq_nonneg (m : ℝ))
  change (commonSquaredSeparation first second : ℝ) * (m : ℝ) ^ 2 ≤
    2 * (commonDenominator m first second : ℝ) ^ 2
  simp only [commonDenominator, Nat.cast_mul]
  convert hScaled using 1 <;> ring


def realSegmentPoint (t : ℝ) (first second : RealPlanePoint) : RealPlanePoint :=
  { x := (1 - t) * first.x + t * second.x
    y := (1 - t) * first.y + t * second.y }


def realPointOfSignedRational (point : SignedRationalPoint) : RealPlanePoint :=
  { x := point.xNumerator / (point.denominator : ℝ)
    y := point.yNumerator / (point.denominator : ℝ) }


def realParameter (parameter : UnitIntervalFraction) : ℝ :=
  parameter.numerator / (parameter.denominator : ℝ)


theorem realParameter_mem_unitInterval (parameter : UnitIntervalFraction) :
    0 ≤ realParameter parameter ∧ realParameter parameter ≤ 1 := by
  constructor
  · unfold realParameter
    positivity
  · unfold realParameter
    apply (div_le_iff₀ (by exact_mod_cast parameter.denominator_pos)).2
    norm_num
    exact_mod_cast parameter.numerator_le_denominator


theorem rational_trace_compatibility {m : ℕ} (hm : 0 < m)
    (parameter : UnitIntervalFraction) (first second : CrossingEdge m) :
    realSegmentPoint (realParameter parameter)
        (firstRealEndpoint first second) (secondRealEndpoint first second) =
      realPointOfSignedRational (segmentPoint hm parameter first second) := by
  apply RealPlanePoint.ext <;>
    simp only [realSegmentPoint, realParameter, firstRealEndpoint, secondRealEndpoint,
      realPointOfSignedRational, segmentPoint, segmentXNumerator, segmentYNumerator,
      segmentInnerWeight, segmentOuterWeight, segmentDenominator]
  all_goals
    have hParameter : (parameter.denominator : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt parameter.denominator_pos
    have hCommon : realCommonDenominator first second ≠ 0 :=
      ne_of_gt (realCommonDenominator_pos hm first second)
    field_simp [realCommonDenominator, hParameter, hCommon]
    push_cast
    ring


theorem continuous_realSegmentPoint_x (first second : RealPlanePoint) :
    Continuous (fun t : ℝ => (realSegmentPoint t first second).x) := by
  unfold realSegmentPoint
  fun_prop


theorem continuous_realSegmentPoint_y (first second : RealPlanePoint) :
    Continuous (fun t : ℝ => (realSegmentPoint t first second).y) := by
  unfold realSegmentPoint
  fun_prop


def realSegmentResidual {m : ℕ} (t : ℝ)
    (first second : CrossingEdge m) : ℝ :=
  (1 - t) * firstRealResidual first second +
    t * secondRealResidual first second +
    t * (1 - t) * squaredDistance
      (firstRealEndpoint first second) (secondRealEndpoint first second)


theorem affine_radius_deficit_identity (t : ℝ)
    (first second : RealPlanePoint) :
    2 - squaredRadius (realSegmentPoint t first second) =
      (1 - t) * (2 - squaredRadius first) +
      t * (2 - squaredRadius second) +
      t * (1 - t) * squaredDistance first second := by
  unfold squaredRadius realSegmentPoint squaredDistance
  dsimp
  ring


theorem real_segment_radius_deficit_exact {m : ℕ} (hm : 0 < m)
    (t : ℝ) (first second : CrossingEdge m) :
    2 - squaredRadius
        (realSegmentPoint t (firstRealEndpoint first second) (secondRealEndpoint first second)) =
      realSegmentResidual t first second := by
  rw [affine_radius_deficit_identity,
    first_radius_deficit_exact hm, second_radius_deficit_exact hm]
  rfl


theorem real_segment_residual_nonneg {m : ℕ} (hm : 0 < m)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (first second : CrossingEdge m) :
    0 ≤ realSegmentResidual t first second := by
  have hw : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hd : 0 ≤ squaredDistance
      (firstRealEndpoint first second) (secondRealEndpoint first second) := by
    unfold squaredDistance
    positivity
  have hf := firstRealResidual_nonneg hm first second
  have hs := secondRealResidual_nonneg hm first second
  unfold realSegmentResidual
  exact add_nonneg (add_nonneg (mul_nonneg hw hf) (mul_nonneg ht0 hs))
    (mul_nonneg (mul_nonneg ht0 hw) hd)


theorem continuous_realSegmentResidual {m : ℕ}
    (first second : CrossingEdge m) :
    Continuous (fun t : ℝ => realSegmentResidual t first second) := by
  unfold realSegmentResidual squaredDistance firstRealEndpoint secondRealEndpoint
  fun_prop


theorem real_segment_residual_le_three {m : ℕ} (hm : 0 < m)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (cell : LocalPolygonalContour.GridCell m)
    (firstSide secondSide : LocalPolygonalContour.CellSide)
    (firstCrossing : firstSide ∈ LocalPolygonalContour.crossingSides cell)
    (secondCrossing : secondSide ∈ LocalPolygonalContour.crossingSides cell) :
    let first := LocalPolygonalContour.crossingEdgeForSide cell firstSide firstCrossing
    let second := LocalPolygonalContour.crossingEdgeForSide cell secondSide secondCrossing
    realSegmentResidual t first second ≤ 3 * inverseCellSquare m := by
  dsimp only
  let first := LocalPolygonalContour.crossingEdgeForSide cell firstSide firstCrossing
  let second := LocalPolygonalContour.crossingEdgeForSide cell secondSide secondCrossing
  have hw : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hi : 0 ≤ inverseCellSquare m := by unfold inverseCellSquare; positivity
  have hFirst := firstRealResidual_le hm first second
  have hSecond := secondRealResidual_le hm first second
  have hFirstWeighted := mul_le_mul_of_nonneg_left hFirst hw
  have hSecondWeighted := mul_le_mul_of_nonneg_left hSecond ht0
  have hEndpoints :
      (1 - t) * firstRealResidual first second + t * secondRealResidual first second ≤
        inverseCellSquare m := by
    nlinarith
  have hDistance := endpoint_squaredDistance_le hm cell firstSide secondSide firstCrossing secondCrossing
  have hCoeff0 : 0 ≤ t * (1 - t) := mul_nonneg ht0 hw
  have hCoeff1 : t * (1 - t) ≤ 1 := by
    nlinarith [sq_nonneg (t - (1 / 2 : ℝ))]
  have hChordScaled := mul_le_mul_of_nonneg_left hDistance hCoeff0
  have hChordCap := mul_le_mul_of_nonneg_right hCoeff1 (by positivity : 0 ≤ 2 * inverseCellSquare m)
  have hChord : t * (1 - t) * squaredDistance
      (firstRealEndpoint first second) (secondRealEndpoint first second) ≤
      2 * inverseCellSquare m := by
    exact le_trans hChordScaled (by simpa using hChordCap)
  unfold realSegmentResidual
  nlinarith


theorem local_segment_every_real_point_exact_and_bounded {m : ℕ} (hm : 0 < m)
    (segment : LocalPolygonalContour.LocalContourSegment m)
    (firstVertex secondVertex : LocalPolygonalContour.SegmentVertex segment)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let first := segmentEdge segment firstVertex
    let second := segmentEdge segment secondVertex
    2 - squaredRadius
          (realSegmentPoint t (firstRealEndpoint first second) (secondRealEndpoint first second)) =
        realSegmentResidual t first second ∧
      0 ≤ realSegmentResidual t first second ∧
      realSegmentResidual t first second ≤ 3 * inverseCellSquare m := by
  dsimp only
  let first := segmentEdge segment firstVertex
  let second := segmentEdge segment secondVertex
  refine ⟨real_segment_radius_deficit_exact hm t first second,
    real_segment_residual_nonneg hm ht0 ht1 first second, ?_⟩
  exact real_segment_residual_le_three hm ht0 ht1 segment.cell
    firstVertex.val secondVertex.val firstVertex.property secondVertex.property


theorem three_inverse_cell_square_epsilon
    (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ N : ℕ, 0 < N ∧ ∀ m : ℕ, N ≤ m →
      3 * inverseCellSquare m < epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / epsilon)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  intro m hm
  have hnm : n < m := lt_of_lt_of_le (Nat.lt_succ_self n) hm
  have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
  have hmPosNat : 0 < m := lt_of_le_of_lt (Nat.zero_le n) hnm
  have hmPos : (0 : ℝ) < m := by exact_mod_cast hmPosNat
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hmPosNat
  have hmSq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hLarge : 3 / epsilon < (m : ℝ) ^ 2 :=
    lt_of_lt_of_le (lt_trans hn hnmR) hmSq
  have hProduct : 3 < epsilon * (m : ℝ) ^ 2 := by
    have := (div_lt_iff₀ hEpsilon).mp hLarge
    nlinarith
  change 3 * (1 / (m : ℝ) ^ 2) < epsilon
  rw [mul_one_div]
  exact (div_lt_iff₀ (sq_pos_of_pos hmPos)).2 (by nlinarith)

end
end LocalSegmentRealCompletion
end BoundaryOfSelf
