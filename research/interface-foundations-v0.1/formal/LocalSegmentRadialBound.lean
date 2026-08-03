import InterpolatedSignedCoordinates

namespace BoundaryOfSelf
namespace LocalSegmentRadialBound

open RationalBoundaryLimit
open RefinedCurvedBoundaryGrid
open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open LocalPolygonalContour
open InterpolatedCurvatureResidual
open InterpolatedSignedCoordinates

/-! IF-BS-22C probe. -/

def uncenteredXNumerator {m : Nat} (edge : CrossingEdge m) : Nat :=
  (interpolationDenominator edge - interpolationNumerator edge) *
      (innerPoint edge).x +
    interpolationNumerator edge * (outerPoint edge).x

def uncenteredYNumerator {m : Nat} (edge : CrossingEdge m) : Nat :=
  (interpolationDenominator edge - interpolationNumerator edge) *
      (innerPoint edge).y +
    interpolationNumerator edge * (outerPoint edge).y

private theorem split_weight_center (d n c : Int) :
    (d - n) * c + n * c = d * c := by
  rw [Int.sub_mul]
  omega

theorem interpolatedXNumerator_eq_uncentered {m : Nat}
    (edge : CrossingEdge m) :
    interpolatedXNumerator edge =
      (uncenteredXNumerator edge : Int) -
        (interpolationDenominator edge * centerCoordinate m : Nat) := by
  have hnle := interpolationNumerator_le_denominator edge
  unfold interpolatedXNumerator innerWeight outerWeight centeredX
    uncenteredXNumerator
  simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_sub hnle]
  rw [Int.mul_sub, Int.mul_sub]
  have hcenter := split_weight_center
    (interpolationDenominator edge : Int)
    (interpolationNumerator edge : Int) (centerCoordinate m : Int)
  omega

theorem interpolatedYNumerator_eq_uncentered {m : Nat}
    (edge : CrossingEdge m) :
    interpolatedYNumerator edge =
      (uncenteredYNumerator edge : Int) -
        (interpolationDenominator edge * centerCoordinate m : Nat) := by
  have hnle := interpolationNumerator_le_denominator edge
  unfold interpolatedYNumerator innerWeight outerWeight centeredY
    uncenteredYNumerator
  simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_sub hnle]
  rw [Int.mul_sub, Int.mul_sub]
  have hcenter := split_weight_center
    (interpolationDenominator edge : Int)
    (interpolationNumerator edge : Int) (centerCoordinate m : Int)
  omega

theorem weighted_between {d n a b lower upper : Nat}
    (hn : n <= d) (haLower : lower <= a) (hbLower : lower <= b)
    (haUpper : a <= upper) (hbUpper : b <= upper) :
    d * lower <= (d - n) * a + n * b /\
      (d - n) * a + n * b <= d * upper := by
  have lowerSplit :
      (d - n) * lower + n * lower = d * lower := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hn]
  have upperSplit :
      (d - n) * upper + n * upper = d * upper := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hn]
  constructor
  · rw [← lowerSplit]
    exact Nat.add_le_add
      (Nat.mul_le_mul_left (d - n) haLower)
      (Nat.mul_le_mul_left n hbLower)
  · rw [← upperSplit]
    exact Nat.add_le_add
      (Nat.mul_le_mul_left (d - n) haUpper)
      (Nat.mul_le_mul_left n hbUpper)

def InCellCoordinates {m : Nat} (cell : GridCell m)
    (point : GridSample m) : Prop :=
  cell.x <= point.x /\ point.x <= cell.x + 1 /\
  cell.y <= point.y /\ point.y <= cell.y + 1

theorem sideStart_in_cell {m : Nat} (cell : GridCell m) (side : CellSide) :
    InCellCoordinates cell (sideStart cell side) := by
  cases side <;>
    simp [InCellCoordinates, sideStart, southWest, southEast,
      northEast, northWest]

theorem sideEnd_in_cell {m : Nat} (cell : GridCell m) (side : CellSide) :
    InCellCoordinates cell (sideEnd cell side) := by
  cases side <;>
    simp [InCellCoordinates, sideEnd, southWest, southEast,
      northEast, northWest]

theorem oriented_side_points_in_cell {m : Nat} (cell : GridCell m)
    (side : CellSide) (crossing : side ∈ crossingSides cell) :
    let edge := crossingEdgeForSide cell side crossing
    InCellCoordinates cell (innerPoint edge) /\
      InCellCoordinates cell (outerPoint edge) := by
  let edge := crossingEdgeForSide cell side crossing
  have hStart := sideStart_in_cell cell side
  have hEnd := sideEnd_in_cell cell side
  dsimp only
  unfold innerPoint outerPoint
  split
  · exact ⟨hStart, hEnd⟩
  · exact ⟨hEnd, hStart⟩

theorem side_crossing_x_bounds {m : Nat} (cell : GridCell m)
    (side : CellSide) (crossing : side ∈ crossingSides cell) :
    let edge := crossingEdgeForSide cell side crossing
    interpolationDenominator edge * cell.x <= uncenteredXNumerator edge /\
      uncenteredXNumerator edge <=
        interpolationDenominator edge * (cell.x + 1) := by
  let edge := crossingEdgeForSide cell side crossing
  have hPoints := oriented_side_points_in_cell cell side crossing
  have hWeight := weighted_between
    (interpolationNumerator_le_denominator edge)
    hPoints.1.1 hPoints.2.1 hPoints.1.2.1 hPoints.2.2.1
  exact hWeight

theorem side_crossing_y_bounds {m : Nat} (cell : GridCell m)
    (side : CellSide) (crossing : side ∈ crossingSides cell) :
    let edge := crossingEdgeForSide cell side crossing
    interpolationDenominator edge * cell.y <= uncenteredYNumerator edge /\
      uncenteredYNumerator edge <=
        interpolationDenominator edge * (cell.y + 1) := by
  let edge := crossingEdgeForSide cell side crossing
  have hPoints := oriented_side_points_in_cell cell side crossing
  have hWeight := weighted_between
    (interpolationNumerator_le_denominator edge)
    hPoints.1.2.2.1 hPoints.2.2.2.1
    hPoints.1.2.2.2 hPoints.2.2.2.2
  exact hWeight

theorem common_fraction_distance_le
    {dFirst dSecond first second base : Nat}
    (firstLower : dFirst * base <= first)
    (firstUpper : first <= dFirst * (base + 1))
    (secondLower : dSecond * base <= second)
    (secondUpper : second <= dSecond * (base + 1)) :
    natDistance (dSecond * first) (dFirst * second) <=
      dFirst * dSecond := by
  let scale := dFirst * dSecond
  have hFirstLower : scale * base <= dSecond * first := by
    have h := Nat.mul_le_mul_left dSecond firstLower
    simpa [scale, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hFirstUpper : dSecond * first <= scale * (base + 1) := by
    have h := Nat.mul_le_mul_left dSecond firstUpper
    simpa [scale, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hSecondLower : scale * base <= dFirst * second := by
    have h := Nat.mul_le_mul_left dFirst secondLower
    simpa [scale, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hSecondUpper : dFirst * second <= scale * (base + 1) := by
    have h := Nat.mul_le_mul_left dFirst secondUpper
    simpa [scale, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hSpan : scale * (base + 1) = scale * base + scale := by
    simp [Nat.mul_add]
  unfold natDistance
  split <;> omega

private theorem double_square (a : Nat) :
    a * a + a * a = 2 * a * a := by
  calc
    a * a + a * a = 2 * (a * a) := by omega
    _ = 2 * a * a := by rw [Nat.mul_assoc]

def commonXFirst {m : Nat} (first second : CrossingEdge m) : Nat :=
  interpolationDenominator second * uncenteredXNumerator first

def commonXSecond {m : Nat} (first second : CrossingEdge m) : Nat :=
  interpolationDenominator first * uncenteredXNumerator second

def commonYFirst {m : Nat} (first second : CrossingEdge m) : Nat :=
  interpolationDenominator second * uncenteredYNumerator first

def commonYSecond {m : Nat} (first second : CrossingEdge m) : Nat :=
  interpolationDenominator first * uncenteredYNumerator second

def commonSquaredSeparation {m : Nat}
    (first second : CrossingEdge m) : Nat :=
  natDistance (commonXFirst first second) (commonXSecond first second) *
      natDistance (commonXFirst first second) (commonXSecond first second) +
    natDistance (commonYFirst first second) (commonYSecond first second) *
      natDistance (commonYFirst first second) (commonYSecond first second)

theorem same_cell_common_separation_le {m : Nat} (cell : GridCell m)
    (firstSide secondSide : CellSide)
    (firstCrossing : firstSide ∈ crossingSides cell)
    (secondCrossing : secondSide ∈ crossingSides cell) :
    let first := crossingEdgeForSide cell firstSide firstCrossing
    let second := crossingEdgeForSide cell secondSide secondCrossing
    commonSquaredSeparation first second <=
      2 * (interpolationDenominator first *
        interpolationDenominator second) *
        (interpolationDenominator first *
          interpolationDenominator second) := by
  let first := crossingEdgeForSide cell firstSide firstCrossing
  let second := crossingEdgeForSide cell secondSide secondCrossing
  have hFirstX := side_crossing_x_bounds cell firstSide firstCrossing
  have hSecondX := side_crossing_x_bounds cell secondSide secondCrossing
  have hFirstY := side_crossing_y_bounds cell firstSide firstCrossing
  have hSecondY := side_crossing_y_bounds cell secondSide secondCrossing
  have hx :
      natDistance (commonXFirst first second) (commonXSecond first second) <=
        interpolationDenominator first * interpolationDenominator second := by
    exact common_fraction_distance_le
      hFirstX.1 hFirstX.2 hSecondX.1 hSecondX.2
  have hy :
      natDistance (commonYFirst first second) (commonYSecond first second) <=
        interpolationDenominator first * interpolationDenominator second := by
    exact common_fraction_distance_le
      hFirstY.1 hFirstY.2 hSecondY.1 hSecondY.2
  dsimp [first, second] at hx hy ⊢
  have hxSquare := Nat.mul_le_mul hx hx
  have hySquare := Nat.mul_le_mul hy hy
  unfold commonSquaredSeparation
  calc
    natDistance
          (commonXFirst
            (crossingEdgeForSide cell firstSide firstCrossing)
            (crossingEdgeForSide cell secondSide secondCrossing))
          (commonXSecond
            (crossingEdgeForSide cell firstSide firstCrossing)
            (crossingEdgeForSide cell secondSide secondCrossing)) *
        natDistance
          (commonXFirst
            (crossingEdgeForSide cell firstSide firstCrossing)
            (crossingEdgeForSide cell secondSide secondCrossing))
          (commonXSecond
            (crossingEdgeForSide cell firstSide firstCrossing)
            (crossingEdgeForSide cell secondSide secondCrossing)) +
      natDistance
          (commonYFirst
            (crossingEdgeForSide cell firstSide firstCrossing)
            (crossingEdgeForSide cell secondSide secondCrossing))
          (commonYSecond
            (crossingEdgeForSide cell firstSide firstCrossing)
            (crossingEdgeForSide cell secondSide secondCrossing)) *
        natDistance
          (commonYFirst
            (crossingEdgeForSide cell firstSide firstCrossing)
            (crossingEdgeForSide cell secondSide secondCrossing))
          (commonYSecond
            (crossingEdgeForSide cell firstSide firstCrossing)
            (crossingEdgeForSide cell secondSide secondCrossing)) <=
        (interpolationDenominator
            (crossingEdgeForSide cell firstSide firstCrossing) *
          interpolationDenominator
            (crossingEdgeForSide cell secondSide secondCrossing)) *
          (interpolationDenominator
              (crossingEdgeForSide cell firstSide firstCrossing) *
            interpolationDenominator
              (crossingEdgeForSide cell secondSide secondCrossing)) +
        (interpolationDenominator
            (crossingEdgeForSide cell firstSide firstCrossing) *
          interpolationDenominator
            (crossingEdgeForSide cell secondSide secondCrossing)) *
          (interpolationDenominator
              (crossingEdgeForSide cell firstSide firstCrossing) *
            interpolationDenominator
              (crossingEdgeForSide cell secondSide secondCrossing)) :=
      Nat.add_le_add hxSquare hySquare
    _ = 2 *
        (interpolationDenominator
            (crossingEdgeForSide cell firstSide firstCrossing) *
          interpolationDenominator
            (crossingEdgeForSide cell secondSide secondCrossing)) *
        (interpolationDenominator
            (crossingEdgeForSide cell firstSide firstCrossing) *
            interpolationDenominator
              (crossingEdgeForSide cell secondSide secondCrossing)) :=
      double_square _

def commonScale {m : Nat} (first second : CrossingEdge m) : Nat :=
  interpolationDenominator first * interpolationDenominator second

def commonDenominator {m : Nat} (scale : Nat)
    (first second : CrossingEdge m) : Nat :=
  commonScale first second * scale

def commonCenteredXFirst {m : Nat}
    (first second : CrossingEdge m) : Int :=
  (interpolationDenominator second : Int) *
    interpolatedXNumerator first

def commonCenteredXSecond {m : Nat}
    (first second : CrossingEdge m) : Int :=
  (interpolationDenominator first : Int) *
    interpolatedXNumerator second

def commonCenteredYFirst {m : Nat}
    (first second : CrossingEdge m) : Int :=
  (interpolationDenominator second : Int) *
    interpolatedYNumerator first

def commonCenteredYSecond {m : Nat}
    (first second : CrossingEdge m) : Int :=
  (interpolationDenominator first : Int) *
    interpolatedYNumerator second

private theorem scaled_center_cancel
    (dFirst dSecond first second center : Nat) :
    (dSecond : Int) * ((first : Int) - (dFirst * center : Nat)) -
        (dFirst : Int) * ((second : Int) - (dSecond * center : Nat)) =
      (dSecond * first : Nat) - (dFirst * second : Nat) := by
  simp only [Int.natCast_mul, Int.mul_sub]
  simp [Int.sub_eq_add_neg,
    Int.mul_left_comm,
    Int.add_assoc]
  omega

theorem common_centered_separation_exact {m : Nat}
    (first second : CrossingEdge m) :
    (commonCenteredXFirst first second -
        commonCenteredXSecond first second) *
        (commonCenteredXFirst first second -
          commonCenteredXSecond first second) +
      (commonCenteredYFirst first second -
        commonCenteredYSecond first second) *
        (commonCenteredYFirst first second -
          commonCenteredYSecond first second) =
      (commonSquaredSeparation first second : Int) := by
  have hxCancel := scaled_center_cancel
    (interpolationDenominator first) (interpolationDenominator second)
    (uncenteredXNumerator first) (uncenteredXNumerator second)
    (centerCoordinate m)
  have hyCancel := scaled_center_cancel
    (interpolationDenominator first) (interpolationDenominator second)
    (uncenteredYNumerator first) (uncenteredYNumerator second)
    (centerCoordinate m)
  have hxSquare := centered_square
    (commonXFirst first second) (commonXSecond first second)
  have hySquare := centered_square
    (commonYFirst first second) (commonYSecond first second)
  unfold commonXFirst commonXSecond at hxSquare
  unfold commonYFirst commonYSecond at hySquare
  simp only [Int.natCast_mul] at hxSquare hySquare
  unfold commonCenteredXFirst commonCenteredXSecond
    commonCenteredYFirst commonCenteredYSecond
  rw [interpolatedXNumerator_eq_uncentered,
    interpolatedXNumerator_eq_uncentered,
    interpolatedYNumerator_eq_uncentered,
    interpolatedYNumerator_eq_uncentered]
  change
    ((interpolationDenominator second : Int) *
          ((uncenteredXNumerator first : Int) -
            (interpolationDenominator first * centerCoordinate m : Nat)) -
        (interpolationDenominator first : Int) *
          ((uncenteredXNumerator second : Int) -
            (interpolationDenominator second * centerCoordinate m : Nat))) *
        ((interpolationDenominator second : Int) *
          ((uncenteredXNumerator first : Int) -
            (interpolationDenominator first * centerCoordinate m : Nat)) -
        (interpolationDenominator first : Int) *
          ((uncenteredXNumerator second : Int) -
            (interpolationDenominator second * centerCoordinate m : Nat))) +
      ((interpolationDenominator second : Int) *
          ((uncenteredYNumerator first : Int) -
            (interpolationDenominator first * centerCoordinate m : Nat)) -
        (interpolationDenominator first : Int) *
          ((uncenteredYNumerator second : Int) -
            (interpolationDenominator second * centerCoordinate m : Nat))) *
        ((interpolationDenominator second : Int) *
          ((uncenteredYNumerator first : Int) -
            (interpolationDenominator first * centerCoordinate m : Nat)) -
        (interpolationDenominator first : Int) *
          ((uncenteredYNumerator second : Int) -
            (interpolationDenominator second * centerCoordinate m : Nat))) =
      (commonSquaredSeparation first second : Int)
  rw [hxCancel, hyCancel]
  unfold commonSquaredSeparation commonXFirst commonXSecond
    commonYFirst commonYSecond
  simp only [Int.natCast_add, Int.natCast_mul]
  rw [hxSquare, hySquare]

def commonFirstResidual {m : Nat}
    (first second : CrossingEdge m) : Nat :=
  interpolationDenominator second * interpolationDenominator second *
    curvatureResidualNumerator first

def commonSecondResidual {m : Nat}
    (first second : CrossingEdge m) : Nat :=
  interpolationDenominator first * interpolationDenominator first *
    curvatureResidualNumerator second

def commonTargetCircleNumerator {m : Nat} (scale : Nat)
    (first second : CrossingEdge m) : Int :=
  2 * (commonDenominator scale first second : Int) *
    (commonDenominator scale first second : Int)

private theorem scale_radius_identity
    (scale x y residual target : Int)
    (h : x * x + y * y + residual = target) :
    (scale * x) * (scale * x) + (scale * y) * (scale * y) +
        scale * scale * residual =
      scale * scale * target := by
  rw [← h]
  simp [Int.mul_add, Int.mul_comm, Int.mul_left_comm, Int.add_comm]

theorem common_first_radius_identity {m : Nat} (hm : 0 < m)
    (first second : CrossingEdge m) :
    commonCenteredXFirst first second * commonCenteredXFirst first second +
        commonCenteredYFirst first second * commonCenteredYFirst first second +
        (commonFirstResidual first second : Int) =
      commonTargetCircleNumerator m first second := by
  have h := scale_radius_identity
    (interpolationDenominator second : Int)
    (interpolatedXNumerator first) (interpolatedYNumerator first)
    (curvatureResidualNumerator first : Int)
    (targetCircleNumerator (interpolatedSignedPoint hm first))
    (interpolation_squared_radius_deficit_exact hm first)
  simpa [commonCenteredXFirst, commonCenteredYFirst,
    commonFirstResidual, commonTargetCircleNumerator, commonDenominator,
    commonScale, targetCircleNumerator, interpolatedSignedPoint,
    Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using h

theorem common_second_radius_identity {m : Nat} (hm : 0 < m)
    (first second : CrossingEdge m) :
    commonCenteredXSecond first second * commonCenteredXSecond first second +
        commonCenteredYSecond first second * commonCenteredYSecond first second +
        (commonSecondResidual first second : Int) =
      commonTargetCircleNumerator m first second := by
  have h := scale_radius_identity
    (interpolationDenominator first : Int)
    (interpolatedXNumerator second) (interpolatedYNumerator second)
    (curvatureResidualNumerator second : Int)
    (targetCircleNumerator (interpolatedSignedPoint hm second))
    (interpolation_squared_radius_deficit_exact hm second)
  simpa [commonCenteredXSecond, commonCenteredYSecond,
    commonSecondResidual, commonTargetCircleNumerator, commonDenominator,
    commonScale, targetCircleNumerator, interpolatedSignedPoint,
    Int.mul_comm, Int.mul_left_comm, Int.mul_assoc] using h

def segmentInnerWeight (parameter : UnitIntervalFraction) : Int :=
  (parameter.denominator : Int) - (parameter.numerator : Int)

def segmentOuterWeight (parameter : UnitIntervalFraction) : Int :=
  (parameter.numerator : Int)

def segmentXNumerator {m : Nat} (parameter : UnitIntervalFraction)
    (first second : CrossingEdge m) : Int :=
  segmentInnerWeight parameter * commonCenteredXFirst first second +
    segmentOuterWeight parameter * commonCenteredXSecond first second

def segmentYNumerator {m : Nat} (parameter : UnitIntervalFraction)
    (first second : CrossingEdge m) : Int :=
  segmentInnerWeight parameter * commonCenteredYFirst first second +
    segmentOuterWeight parameter * commonCenteredYSecond first second

def segmentDenominator {m : Nat} (scale : Nat)
    (parameter : UnitIntervalFraction)
    (first second : CrossingEdge m) : Nat :=
  parameter.denominator * commonDenominator scale first second

theorem segmentDenominator_pos {m : Nat} (hm : 0 < m)
    (parameter : UnitIntervalFraction) (first second : CrossingEdge m) :
    0 < segmentDenominator m parameter first second := by
  unfold segmentDenominator commonDenominator commonScale
  exact Nat.mul_pos parameter.denominator_pos
    (Nat.mul_pos
      (Nat.mul_pos (interpolationDenominator_pos first)
        (interpolationDenominator_pos second)) hm)

def segmentPoint {m : Nat} (hm : 0 < m)
    (parameter : UnitIntervalFraction)
    (first second : CrossingEdge m) : SignedRationalPoint where
  xNumerator := segmentXNumerator parameter first second
  yNumerator := segmentYNumerator parameter first second
  denominator := segmentDenominator m parameter first second
  denominator_pos := segmentDenominator_pos hm parameter first second

def segmentResidualNumerator {m : Nat}
    (parameter : UnitIntervalFraction)
    (first second : CrossingEdge m) : Nat :=
  parameter.denominator *
      (parameter.denominator - parameter.numerator) *
      commonFirstResidual first second +
    parameter.denominator * parameter.numerator *
      commonSecondResidual first second +
    parameter.numerator *
      (parameter.denominator - parameter.numerator) *
      commonSquaredSeparation first second

private theorem segment_deficit_algebra
    (r k target firstResidual secondResidual separation : Int) :
    r * (r - k) * (target - firstResidual) +
          r * k * (target - secondResidual) -
          k * (r - k) * separation +
        (r * (r - k) * firstResidual +
          r * k * secondResidual +
          k * (r - k) * separation) =
      r * r * target := by
  simp [Int.sub_eq_add_neg, Int.mul_add, Int.mul_neg,
    Int.mul_comm, Int.mul_left_comm,
    Int.add_assoc]
  omega

private theorem squared_difference_comm (a b : Int) :
    (a - b) * (a - b) = (b - a) * (b - a) := by
  have hneg : a - b = -(b - a) := by omega
  rw [hneg, Int.neg_mul, Int.mul_neg, Int.neg_neg]

theorem segment_raw_radius_identity {m : Nat} (hm : 0 < m)
    (parameter : UnitIntervalFraction)
    (first second : CrossingEdge m) :
    segmentXNumerator parameter first second *
          segmentXNumerator parameter first second +
        segmentYNumerator parameter first second *
          segmentYNumerator parameter first second +
        (segmentResidualNumerator parameter first second : Int) =
      (parameter.denominator : Int) * (parameter.denominator : Int) *
        commonTargetCircleNumerator m first second := by
  have hvector := weighted_vector_square_identity
    (parameter.denominator : Int) (parameter.numerator : Int)
    (commonCenteredXFirst first second)
    (commonCenteredYFirst first second)
    (commonCenteredXSecond first second)
    (commonCenteredYSecond first second)
  have hFirst := common_first_radius_identity hm first second
  have hSecond := common_second_radius_identity hm first second
  have hSeparation := common_centered_separation_exact first second
  have hSeparationReverse :
      (commonCenteredXSecond first second -
          commonCenteredXFirst first second) *
          (commonCenteredXSecond first second -
            commonCenteredXFirst first second) +
        (commonCenteredYSecond first second -
          commonCenteredYFirst first second) *
          (commonCenteredYSecond first second -
            commonCenteredYFirst first second) =
        (commonSquaredSeparation first second : Int) := by
    calc
      (commonCenteredXSecond first second -
            commonCenteredXFirst first second) *
            (commonCenteredXSecond first second -
              commonCenteredXFirst first second) +
          (commonCenteredYSecond first second -
            commonCenteredYFirst first second) *
            (commonCenteredYSecond first second -
              commonCenteredYFirst first second) =
        (commonCenteredXFirst first second -
            commonCenteredXSecond first second) *
            (commonCenteredXFirst first second -
              commonCenteredXSecond first second) +
          (commonCenteredYFirst first second -
            commonCenteredYSecond first second) *
            (commonCenteredYFirst first second -
              commonCenteredYSecond first second) := by
                rw [squared_difference_comm
                    (commonCenteredXSecond first second)
                    (commonCenteredXFirst first second),
                  squared_difference_comm
                    (commonCenteredYSecond first second)
                    (commonCenteredYFirst first second)]
      _ = (commonSquaredSeparation first second : Int) := hSeparation
  have hFirstNorm :
      commonCenteredXFirst first second * commonCenteredXFirst first second +
          commonCenteredYFirst first second * commonCenteredYFirst first second =
        commonTargetCircleNumerator m first second -
          (commonFirstResidual first second : Int) := by omega
  have hSecondNorm :
      commonCenteredXSecond first second * commonCenteredXSecond first second +
          commonCenteredYSecond first second * commonCenteredYSecond first second =
        commonTargetCircleNumerator m first second -
          (commonSecondResidual first second : Int) := by omega
  rw [hFirstNorm, hSecondNorm, hSeparationReverse] at hvector
  unfold segmentXNumerator segmentYNumerator segmentInnerWeight
    segmentOuterWeight
  rw [hvector]
  unfold segmentResidualNumerator
  simp only [Int.natCast_add, Int.natCast_mul,
    Int.natCast_sub parameter.numerator_le_denominator]
  exact segment_deficit_algebra
    (parameter.denominator : Int) (parameter.numerator : Int)
    (commonTargetCircleNumerator m first second)
    (commonFirstResidual first second : Int)
    (commonSecondResidual first second : Int)
    (commonSquaredSeparation first second : Int)

theorem segment_squared_radius_deficit_exact {m : Nat} (hm : 0 < m)
    (parameter : UnitIntervalFraction)
    (first second : CrossingEdge m) :
    squaredRadiusNumerator (segmentPoint hm parameter first second) +
        (segmentResidualNumerator parameter first second : Int) =
      targetCircleNumerator (segmentPoint hm parameter first second) := by
  have hRaw := segment_raw_radius_identity hm parameter first second
  simpa [squaredRadiusNumerator, segmentPoint, targetCircleNumerator,
    segmentDenominator, commonTargetCircleNumerator, commonDenominator,
    commonScale, Int.mul_left_comm, Int.mul_assoc] using hRaw

theorem commonFirstResidual_le_scaleSquare {m : Nat}
    (first second : CrossingEdge m) :
    commonFirstResidual first second <=
      commonScale first second * commonScale first second := by
  have hResidual := splitProduct_le_square
    (interpolationNumerator first) (interpolationDenominator first)
    (interpolationNumerator_le_denominator first)
  have hScaled := Nat.mul_le_mul_left
    (interpolationDenominator second * interpolationDenominator second)
    hResidual
  unfold commonFirstResidual commonScale curvatureResidualNumerator
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hScaled

theorem commonSecondResidual_le_scaleSquare {m : Nat}
    (first second : CrossingEdge m) :
    commonSecondResidual first second <=
      commonScale first second * commonScale first second := by
  have hResidual := splitProduct_le_square
    (interpolationNumerator second) (interpolationDenominator second)
    (interpolationNumerator_le_denominator second)
  have hScaled := Nat.mul_le_mul_left
    (interpolationDenominator first * interpolationDenominator first)
    hResidual
  unfold commonSecondResidual commonScale curvatureResidualNumerator
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hScaled

theorem weighted_segment_residual_le_three
    {r k bound firstResidual secondResidual separation : Nat}
    (hk : k <= r)
    (hFirst : firstResidual <= bound)
    (hSecond : secondResidual <= bound)
    (hSeparation : separation <= 2 * bound) :
    r * (r - k) * firstResidual + r * k * secondResidual +
        k * (r - k) * separation <=
      3 * r * r * bound := by
  have hFirstScaled := Nat.mul_le_mul_left (r * (r - k)) hFirst
  have hSecondScaled := Nat.mul_le_mul_left (r * k) hSecond
  have hSeparationScaled :=
    Nat.mul_le_mul_left (k * (r - k)) hSeparation
  have hTerms := Nat.add_le_add
    (Nat.add_le_add hFirstScaled hSecondScaled) hSeparationScaled
  have hSplit := splitProduct_le_square k r hk
  have hSplitScaled := Nat.mul_le_mul_right (2 * bound) hSplit
  have hWeights : r - k + k = r := Nat.sub_add_cancel hk
  have hEndpoint :
      r * (r - k) * bound + r * k * bound = r * r * bound := by
    calc
      r * (r - k) * bound + r * k * bound =
          (r * (r - k) + r * k) * bound := by
            rw [Nat.add_mul]
      _ = r * ((r - k) + k) * bound := by
            rw [Nat.mul_add]
      _ = r * r * bound := by rw [hWeights]
  have hThree : bound + 2 * bound = 3 * bound := by omega
  calc
    r * (r - k) * firstResidual + r * k * secondResidual +
        k * (r - k) * separation <=
      r * (r - k) * bound + r * k * bound +
        k * (r - k) * (2 * bound) := hTerms
    _ = r * r * bound + k * (r - k) * (2 * bound) := by
      rw [hEndpoint]
    _ <= r * r * bound + r * r * (2 * bound) :=
      Nat.add_le_add_left hSplitScaled (r * r * bound)
    _ = 3 * r * r * bound := by
      calc
        r * r * bound + r * r * (2 * bound) =
            (r * r) * (bound + 2 * bound) := by rw [Nat.mul_add]
        _ = (r * r) * (3 * bound) := by rw [hThree]
        _ = 3 * r * r * bound := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

set_option maxHeartbeats 500000 in
theorem same_cell_segment_residual_le {m : Nat} (cell : GridCell m)
    (firstSide secondSide : CellSide)
    (firstCrossing : firstSide ∈ crossingSides cell)
    (secondCrossing : secondSide ∈ crossingSides cell)
    (parameter : UnitIntervalFraction) :
    let first := crossingEdgeForSide cell firstSide firstCrossing
    let second := crossingEdgeForSide cell secondSide secondCrossing
    segmentResidualNumerator parameter first second <=
      3 * parameter.denominator * parameter.denominator *
        (commonScale first second * commonScale first second) := by
  let first := crossingEdgeForSide cell firstSide firstCrossing
  let second := crossingEdgeForSide cell secondSide secondCrossing
  have hFirst := commonFirstResidual_le_scaleSquare first second
  have hSecond := commonSecondResidual_le_scaleSquare first second
  have hSeparation := same_cell_common_separation_le cell firstSide secondSide
    firstCrossing secondCrossing
  have hSeparationNormalized :
      commonSquaredSeparation first second <=
        2 * (commonScale first second * commonScale first second) := by
    simpa [commonScale, Nat.mul_assoc] using hSeparation
  have hBound := weighted_segment_residual_le_three
    parameter.numerator_le_denominator hFirst hSecond hSeparationNormalized
  exact hBound

def threeSquaredCellWidth (m : Nat) (hm : 0 < m) : PositiveFraction where
  numerator := 3
  denominator := m * m
  numerator_pos := by omega
  denominator_pos := Nat.mul_pos hm hm

def segmentRadialResidual {m : Nat} (hm : 0 < m)
    (parameter : UnitIntervalFraction)
    (first second : CrossingEdge m) : NonnegativeFraction where
  numerator := segmentResidualNumerator parameter first second
  denominator := segmentDenominator m parameter first second *
    segmentDenominator m parameter first second
  denominator_pos := Nat.mul_pos
    (segmentDenominator_pos hm parameter first second)
    (segmentDenominator_pos hm parameter first second)

theorem same_cell_segment_residual_fraction_le {m : Nat} (hm : 0 < m)
    (cell : GridCell m) (firstSide secondSide : CellSide)
    (firstCrossing : firstSide ∈ crossingSides cell)
    (secondCrossing : secondSide ∈ crossingSides cell)
    (parameter : UnitIntervalFraction) :
    let first := crossingEdgeForSide cell firstSide firstCrossing
    let second := crossingEdgeForSide cell secondSide secondCrossing
    FractionLePositive (segmentRadialResidual hm parameter first second)
      (threeSquaredCellWidth m hm) := by
  let first := crossingEdgeForSide cell firstSide firstCrossing
  let second := crossingEdgeForSide cell secondSide secondCrossing
  have hBound := same_cell_segment_residual_le cell firstSide secondSide
    firstCrossing secondCrossing parameter
  have hScaled := Nat.mul_le_mul_right (m * m) hBound
  dsimp only
  change segmentResidualNumerator parameter first second * (m * m) <=
    3 * (segmentDenominator m parameter first second *
      segmentDenominator m parameter first second)
  simpa [segmentDenominator, commonDenominator, commonScale,
    Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hScaled

theorem three_squared_cell_width_limit :
    forall epsilon : PositiveFraction, exists N : Nat,
      0 < N /\ forall (m : Nat) (hm : 0 < m), N <= m ->
        FractionLt (threeSquaredCellWidth m hm) epsilon := by
  intro epsilon
  let N := 3 * epsilon.denominator + 1
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    omega
  · intro m hm hNm
    have hDenominator : 3 * epsilon.denominator < m := by
      dsimp [N] at hNm
      omega
    have hOne : 1 <= m := hm
    have hSquare : m <= m * m := by
      have h := Nat.mul_le_mul_left m hOne
      simpa using h
    have hNumerator : 1 <= epsilon.numerator := epsilon.numerator_pos
    have hScaled : m * m <= epsilon.numerator * (m * m) := by
      have h := Nat.mul_le_mul_right (m * m) hNumerator
      simpa using h
    unfold FractionLt threeSquaredCellWidth
    exact Nat.lt_of_lt_of_le hDenominator
      (Nat.le_trans hSquare hScaled)

def segmentEdge {m : Nat} (segment : LocalContourSegment m)
    (vertex : SegmentVertex segment) : CrossingEdge m :=
  crossingEdgeForSide segment.cell vertex.val vertex.property

theorem local_segment_every_rational_point_exact_and_bounded {m : Nat}
    (hm : 0 < m) (segment : LocalContourSegment m)
    (firstVertex secondVertex : SegmentVertex segment)
    (parameter : UnitIntervalFraction) :
    let first := segmentEdge segment firstVertex
    let second := segmentEdge segment secondVertex
    squaredRadiusNumerator (segmentPoint hm parameter first second) +
          (segmentResidualNumerator parameter first second : Int) =
        targetCircleNumerator (segmentPoint hm parameter first second) /\
      FractionLePositive (segmentRadialResidual hm parameter first second)
        (threeSquaredCellWidth m hm) := by
  let first := segmentEdge segment firstVertex
  let second := segmentEdge segment secondVertex
  constructor
  · exact segment_squared_radius_deficit_exact hm parameter first second
  · exact same_cell_segment_residual_fraction_le hm segment.cell
      firstVertex.val secondVertex.val firstVertex.property
      secondVertex.property parameter

theorem local_segment_radial_bound_limit :
    forall epsilon : PositiveFraction, exists N : Nat,
      0 < N /\ forall (m : Nat) (hm : 0 < m), N <= m ->
        FractionLt (threeSquaredCellWidth m hm) epsilon /\
        forall (segment : LocalContourSegment m)
          (firstVertex secondVertex : SegmentVertex segment)
          (parameter : UnitIntervalFraction),
          FractionLePositive
            (segmentRadialResidual hm parameter
              (segmentEdge segment firstVertex)
              (segmentEdge segment secondVertex))
            (threeSquaredCellWidth m hm) := by
  intro epsilon
  rcases three_squared_cell_width_limit epsilon with ⟨N, hN, hLimit⟩
  refine ⟨N, hN, ?_⟩
  intro m hm hNm
  refine ⟨hLimit m hm hNm, ?_⟩
  intro segment firstVertex secondVertex parameter
  exact same_cell_segment_residual_fraction_le hm segment.cell
    firstVertex.val secondVertex.val firstVertex.property
    secondVertex.property parameter

end LocalSegmentRadialBound
end BoundaryOfSelf
