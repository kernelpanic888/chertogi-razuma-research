import DominantCoordinateMetricPrelude

namespace BoundaryOfSelf
namespace GridPhysicalCoordinateAdapter

noncomputable section

open UniformRadialBoundaryFamily
open InterpolatedSignedCoordinates
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open CircleAxisRounding
open DominantCoordinateMetricPrelude

/-!
IF-BS-22F-B3C2B2A transports finite radial-grid samples to the real plane.
The normalization sends the grid centre 2m to zero and one grid edge to 1/m.
It converts the exact natural-number threshold into the ordinary radius-two
inequalities required by the dominant-coordinate metric prelude.
-/

def physicalX {m : Nat} (sample : GridSample m) : Real :=
  (sample.x : Real) / (m : Real) - 2

def physicalY {m : Nat} (sample : GridSample m) : Real :=
  (sample.y : Real) / (m : Real) - 2

def physicalPoint {m : Nat} (sample : GridSample m) : RealPlanePoint :=
  { x := physicalX sample, y := physicalY sample }

theorem physicalX_eq_centered {m : Nat} (hm : 0 < m)
    (sample : GridSample m) :
    physicalX sample = ((centeredX sample : Int) : Real) / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  unfold physicalX centeredX centerCoordinate
  push_cast
  field_simp [ne_of_gt hmReal]

theorem physicalY_eq_centered {m : Nat} (hm : 0 < m)
    (sample : GridSample m) :
    physicalY sample = ((centeredY sample : Int) : Real) / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  unfold physicalY centeredY centerCoordinate
  push_cast
  field_simp [ne_of_gt hmReal]

theorem physicalPoint_squaredRadius {m : Nat} (hm : 0 < m)
    (sample : GridSample m) :
    squaredRadius (physicalPoint sample) =
      (radialNumerator sample : Real) / (m : Real) ^ 2 := by
  have hCentered := centered_radius sample
  have hCenteredReal :
      (((centeredX sample : Int) : Real) ^ 2 +
        ((centeredY sample : Int) : Real) ^ 2) =
          (radialNumerator sample : Real) := by
    have hCast :
        ((centeredX sample : Int) : Real) *
            ((centeredX sample : Int) : Real) +
          ((centeredY sample : Int) : Real) *
            ((centeredY sample : Int) : Real) =
              (radialNumerator sample : Real) := by
      exact_mod_cast hCentered
    simpa [pow_two] using hCast
  rw [squaredRadius, physicalPoint]
  dsimp
  rw [physicalX_eq_centered hm, physicalY_eq_centered hm]
  rw [div_pow, div_pow]
  calc
    ((centeredX sample : Int) : Real) ^ 2 / (m : Real) ^ 2 +
        ((centeredY sample : Int) : Real) ^ 2 / (m : Real) ^ 2 =
      ((((centeredX sample : Int) : Real) ^ 2 +
        ((centeredY sample : Int) : Real) ^ 2) / (m : Real) ^ 2) := by ring
    _ = (radialNumerator sample : Real) / (m : Real) ^ 2 := by
      rw [hCenteredReal]

theorem physicalPoint_inside {m : Nat} (hm : 0 < m)
    (sample : GridSample m) (hInside : Inside sample) :
    squaredRadius (physicalPoint sample) <= 2 := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hmSquare : (0 : Real) < (m : Real) ^ 2 := sq_pos_of_pos hmReal
  rw [physicalPoint_squaredRadius hm]
  apply (div_le_iff₀ hmSquare).2
  unfold Inside thresholdNumerator at hInside
  have hCast :
      (radialNumerator sample : Real) <= ((2 * m * m : Nat) : Real) := by
    exact_mod_cast hInside
  norm_num [Nat.cast_mul] at hCast ⊢
  nlinarith

theorem physicalPoint_outside {m : Nat} (hm : 0 < m)
    (sample : GridSample m) (hOutside : ¬ Inside sample) :
    2 < squaredRadius (physicalPoint sample) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hmSquare : (0 : Real) < (m : Real) ^ 2 := sq_pos_of_pos hmReal
  rw [physicalPoint_squaredRadius hm]
  apply (lt_div_iff₀ hmSquare).2
  unfold Inside thresholdNumerator at hOutside
  have hNatural : 2 * m * m < radialNumerator sample :=
    Nat.lt_of_not_ge hOutside
  have hCast :
      ((2 * m * m : Nat) : Real) < (radialNumerator sample : Real) := by
    exact_mod_cast hNatural
  norm_num [Nat.cast_mul] at hCast ⊢
  nlinarith

theorem physicalX_step_right {m : Nat} (hm : 0 < m)
    (inside outside : GridSample m)
    (hStep : outside.x = inside.x + 1) :
    physicalX outside = physicalX inside + 1 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  unfold physicalX
  rw [hStep]
  push_cast
  field_simp [ne_of_gt hmReal]
  ring

theorem physicalX_step_left {m : Nat} (hm : 0 < m)
    (inside outside : GridSample m)
    (hStep : outside.x + 1 = inside.x) :
    physicalX outside = physicalX inside - 1 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  unfold physicalX
  have hCast : (outside.x : Real) + 1 = (inside.x : Real) := by
    exact_mod_cast hStep
  field_simp [ne_of_gt hmReal]
  nlinarith

theorem physicalY_step_up {m : Nat} (hm : 0 < m)
    (inside outside : GridSample m)
    (hStep : outside.y = inside.y + 1) :
    physicalY outside = physicalY inside + 1 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  unfold physicalY
  rw [hStep]
  push_cast
  field_simp [ne_of_gt hmReal]
  ring

theorem physicalY_step_down {m : Nat} (hm : 0 < m)
    (inside outside : GridSample m)
    (hStep : outside.y + 1 = inside.y) :
    physicalY outside = physicalY inside - 1 / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  unfold physicalY
  have hCast : (outside.y : Real) + 1 = (inside.y : Real) := by
    exact_mod_cast hStep
  field_simp [ne_of_gt hmReal]
  nlinarith

theorem physical_targetAxis {m : Nat} (hm : 0 < m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target) :
    (targetAxis m target : Real) / (m : Real) - 2 =
      inwardRoundedCoordinate m target.y := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hOffset : inwardOffset m target.y <= 2 * m :=
    inwardOffset_le_two_mul (target_y_abs_le_radius hTarget)
  by_cases hSign : 0 <= target.y
  · rw [targetAxis, inwardAxis, if_pos hSign]
    rw [inwardRoundedCoordinate, if_pos hSign]
    push_cast
    field_simp [ne_of_gt hmReal]
    ring
  · rw [targetAxis, inwardAxis, if_neg hSign]
    rw [inwardRoundedCoordinate, if_neg hSign]
    rw [Nat.cast_sub hOffset]
    push_cast
    field_simp [ne_of_gt hmReal]
    ring

theorem physicalY_of_targetAxis {m : Nat} (hm : 0 < m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target)
    (sample : GridSample m) (hAxis : sample.y = targetAxis m target) :
    physicalY sample = inwardRoundedCoordinate m target.y := by
  unfold physicalY
  rw [hAxis]
  exact physical_targetAxis hm target hTarget

theorem physicalX_of_swappedTargetAxis {m : Nat} (hm : 0 < m)
    (target : RealPlanePoint) (hTarget : onTargetCircle target)
    (sample : GridSample m)
    (hAxis : sample.x = targetAxis m (DominantAxisLocalSegment.swapTarget target)) :
    physicalX sample = inwardRoundedCoordinate m target.x := by
  unfold physicalX
  rw [hAxis]
  simpa using physical_targetAxis hm (DominantAxisLocalSegment.swapTarget target)
    (DominantAxisLocalSegment.swapTarget_onTargetCircle hTarget)

end
end GridPhysicalCoordinateAdapter
end BoundaryOfSelf

#print axioms BoundaryOfSelf.GridPhysicalCoordinateAdapter.physicalPoint_squaredRadius
#print axioms BoundaryOfSelf.GridPhysicalCoordinateAdapter.physicalPoint_inside
#print axioms BoundaryOfSelf.GridPhysicalCoordinateAdapter.physicalPoint_outside
#print axioms BoundaryOfSelf.GridPhysicalCoordinateAdapter.physical_targetAxis
