import AxisThresholdSymmetry
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

namespace BoundaryOfSelf
namespace CircleAxisRounding

noncomputable section

open RefinedCurvedBoundaryGrid
open UniformRadialBoundaryFamily
open AxisThresholdBracket
open AxisThresholdSymmetry
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound

/-!
IF-BS-22F-B3A/B chooses a finite-grid axis for an arbitrary real point of the
target circle. The absolute coordinate is rounded down before its sign is
restored. Thus the selected axis always moves toward the centre rather than
possibly crossing outside at a pole.
-/

def inwardOffset (m : Nat) (coordinate : Real) : Nat :=
  Nat.floor ((m : Real) * |coordinate|)

def inwardAxis (m : Nat) (coordinate : Real) : Nat :=
  if 0 <= coordinate then
    2 * m + inwardOffset m coordinate
  else
    2 * m - inwardOffset m coordinate

def inwardRoundedCoordinate (m : Nat) (coordinate : Real) : Real :=
  if 0 <= coordinate then
    (inwardOffset m coordinate : Real) / (m : Real)
  else
    -((inwardOffset m coordinate : Real) / (m : Real))

def targetAxis (m : Nat) (target : RealPlanePoint) : Nat :=
  inwardAxis m target.y

theorem targetRadius_le_two : targetRadius <= 2 := by
  have hRadius := targetRadius_nonneg
  have hSquare := targetRadius_sq
  nlinarith

theorem target_y_square_le_two {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    target.y ^ 2 <= 2 := by
  unfold onTargetCircle squaredRadius at hTarget
  nlinarith [sq_nonneg target.x]

theorem target_y_abs_le_radius {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    |target.y| <= targetRadius := by
  have hSquare : |target.y| ^ 2 <= targetRadius ^ 2 := by
    rw [sq_abs, targetRadius_sq]
    exact target_y_square_le_two hTarget
  exact (sq_le_sq₀ (abs_nonneg target.y) targetRadius_nonneg).mp hSquare

theorem inwardOffset_cast_le (m : Nat) (coordinate : Real) :
    (inwardOffset m coordinate : Real) <= (m : Real) * |coordinate| := by
  unfold inwardOffset
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) (abs_nonneg coordinate))

theorem inwardOffset_lt_add_one (m : Nat) (coordinate : Real) :
    (m : Real) * |coordinate| < (inwardOffset m coordinate : Real) + 1 := by
  simpa [inwardOffset] using
    (Nat.lt_floor_add_one ((m : Real) * |coordinate|))

theorem inwardOffset_le_two_mul {m : Nat} {coordinate : Real}
    (hCoordinate : |coordinate| <= targetRadius) :
    inwardOffset m coordinate <= 2 * m := by
  have hCast : (inwardOffset m coordinate : Real) <= ((2 * m : Nat) : Real) := by
    calc
      (inwardOffset m coordinate : Real) <= (m : Real) * |coordinate| :=
        inwardOffset_cast_le m coordinate
      _ <= (m : Real) * 2 :=
        mul_le_mul_of_nonneg_left
          (le_trans hCoordinate targetRadius_le_two) (Nat.cast_nonneg m)
      _ = ((2 * m : Nat) : Real) := by norm_num; ring
  exact_mod_cast hCast

theorem inwardAxis_le_four_mul {m : Nat} {coordinate : Real}
    (hCoordinate : |coordinate| <= targetRadius) :
    inwardAxis m coordinate <= 4 * m := by
  have hOffset := inwardOffset_le_two_mul (m := m) hCoordinate
  unfold inwardAxis
  split <;> omega

theorem inwardAxis_center_distance {m : Nat} {coordinate : Real}
    (hCoordinate : |coordinate| <= targetRadius) :
    natDistance (inwardAxis m coordinate) (2 * m) =
      inwardOffset m coordinate := by
  have hOffset := inwardOffset_le_two_mul (m := m) hCoordinate
  unfold inwardAxis
  split <;> unfold natDistance <;> split <;> omega

theorem inwardOffset_square_le_threshold {m : Nat}
    {target : RealPlanePoint} (hTarget : onTargetCircle target) :
    inwardOffset m target.y * inwardOffset m target.y <= 2 * m * m := by
  have hFloorNonneg : (0 : Real) <= (inwardOffset m target.y : Real) := by
    positivity
  have hScaledNonneg :
      (0 : Real) <= (m : Real) * |target.y| := by positivity
  have hFloorSquare :
      (inwardOffset m target.y : Real) ^ 2 <=
        ((m : Real) * |target.y|) ^ 2 :=
    (sq_le_sq₀ hFloorNonneg hScaledNonneg).mpr
      (inwardOffset_cast_le m target.y)
  have hScaledSquare :
      ((m : Real) * |target.y|) ^ 2 <= 2 * (m : Real) ^ 2 := by
    calc
      ((m : Real) * |target.y|) ^ 2 =
          (m : Real) ^ 2 * target.y ^ 2 := by rw [mul_pow, sq_abs]
      _ <= (m : Real) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left (target_y_square_le_two hTarget)
          (sq_nonneg (m : Real))
      _ = 2 * (m : Real) ^ 2 := by ring
  have hFinal := le_trans hFloorSquare hScaledSquare
  norm_num [pow_two] at hFinal
  have hNatural :
      inwardOffset m target.y * inwardOffset m target.y <= 2 * (m * m) := by
    exact_mod_cast hFinal
  simpa [Nat.mul_assoc] using hNatural

theorem targetAxis_le_four_mul {m : Nat} {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    targetAxis m target <= 4 * m := by
  exact inwardAxis_le_four_mul (target_y_abs_le_radius hTarget)

theorem targetAxis_center_distance {m : Nat} {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    natDistance (targetAxis m target) (2 * m) = inwardOffset m target.y := by
  exact inwardAxis_center_distance (target_y_abs_le_radius hTarget)

theorem target_axis_center_inside {m : Nat} {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    Inside
      (rightScanSample m (targetAxis m target)
        (targetAxis_le_four_mul hTarget) 0) := by
  rw [rightScanSample_zero]
  unfold Inside radialNumerator xOffset yOffset thresholdNumerator centerCoordinate
  rw [targetAxis_center_distance hTarget]
  simpa [natDistance] using inwardOffset_square_le_threshold hTarget

theorem inwardRoundedCoordinate_error {m : Nat} (hm : 0 < m)
    (coordinate : Real) :
    |coordinate - inwardRoundedCoordinate m coordinate| < 1 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hLower := inwardOffset_cast_le m coordinate
  have hUpper := inwardOffset_lt_add_one m coordinate
  by_cases hSign : 0 <= coordinate
  · rw [inwardRoundedCoordinate, if_pos hSign]
    have hQuotientLe :
        (inwardOffset m coordinate : Real) / (m : Real) <= coordinate := by
      apply (div_le_iff₀ hmReal).mpr
      simpa [abs_of_nonneg hSign, mul_comm] using hLower
    rw [abs_of_nonneg (sub_nonneg.mpr hQuotientLe)]
    apply (lt_div_iff₀ hmReal).mpr
    calc
      (coordinate - (inwardOffset m coordinate : Real) / (m : Real)) *
          (m : Real) =
        coordinate * (m : Real) - (inwardOffset m coordinate : Real) := by
          field_simp [ne_of_gt hmReal] <;> ring
      _ < 1 := by
        rw [abs_of_nonneg hSign] at hUpper
        nlinarith
  · have hNegative : coordinate < 0 := lt_of_not_ge hSign
    rw [inwardRoundedCoordinate, if_neg hSign]
    have hQuotientLe :
        (inwardOffset m coordinate : Real) / (m : Real) <= -coordinate := by
      apply (div_le_iff₀ hmReal).mpr
      simpa [abs_of_neg hNegative, mul_comm] using hLower
    have hSumNonpos :
        coordinate + (inwardOffset m coordinate : Real) / (m : Real) <= 0 := by
      linarith
    rw [sub_neg_eq_add, abs_of_nonpos hSumNonpos]
    apply (lt_div_iff₀ hmReal).mpr
    calc
      (-(coordinate + (inwardOffset m coordinate : Real) / (m : Real))) *
          (m : Real) =
        (-coordinate) * (m : Real) - (inwardOffset m coordinate : Real) := by
          field_simp [ne_of_gt hmReal] <;> ring
      _ < 1 := by
        rw [abs_of_neg hNegative] at hUpper
        nlinarith

theorem target_axis_coordinate_error {m : Nat} (hm : 0 < m)
    (target : RealPlanePoint) :
    |target.y - inwardRoundedCoordinate m target.y| < 1 / (m : Real) :=
  inwardRoundedCoordinate_error hm target.y

theorem target_has_four_axis_crossings {m : Nat} (hm : 0 < m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target) :
    Nonempty (FourAxisCrossings m (targetAxis m target)) := by
  exact exists_four_axis_crossings hm (targetAxis m target)
    (targetAxis_le_four_mul hTarget) (target_axis_center_inside hTarget)

theorem target_has_four_axis_crossings_on_global_orbit {m : Nat} (hm : 0 < m)
    (anchor : ConcreteRadialContourTraversal.ContourState m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target) :
    exists crossings : FourAxisCrossings m (targetAxis m target),
      MinimalSeparatingContourOrbit.OrbitCut
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          crossings.right ∧
        MinimalSeparatingContourOrbit.OrbitCut
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          crossings.left ∧
        MinimalSeparatingContourOrbit.OrbitCut
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          crossings.top ∧
        MinimalSeparatingContourOrbit.OrbitCut
          (ContourOrbitPotentialSeparation.SelectedOrbit hm anchor)
          crossings.bottom := by
  exact exists_four_axis_crossings_on_global_orbit hm anchor
    (targetAxis m target) (targetAxis_le_four_mul hTarget)
    (target_axis_center_inside hTarget)

end
end CircleAxisRounding
end BoundaryOfSelf

#print axioms BoundaryOfSelf.CircleAxisRounding.inwardAxis_center_distance
#print axioms BoundaryOfSelf.CircleAxisRounding.inwardOffset_square_le_threshold
#print axioms BoundaryOfSelf.CircleAxisRounding.target_axis_center_inside
#print axioms BoundaryOfSelf.CircleAxisRounding.inwardRoundedCoordinate_error
#print axioms BoundaryOfSelf.CircleAxisRounding.target_has_four_axis_crossings
#print axioms BoundaryOfSelf.CircleAxisRounding.target_has_four_axis_crossings_on_global_orbit
