import DominantAxisLocalSegment

namespace BoundaryOfSelf
namespace DominantCoordinateMetricPrelude

noncomputable section

open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open CircleAxisRounding

/-!
IF-BS-22F-B3C2B1 is the real-analysis core of the reverse metric estimate.
It is independent of the grid encoding: a target point on x^2+y^2=2 has a
dominant coordinate of magnitude at least one, inward rounding changes the
orthogonal magnitude by less than 1/m, and an adjacent inside/outside radial
bracket interpolates within 3/m of the dominant target coordinate.
-/

theorem target_has_unit_coordinate {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    1 <= |target.x| \/ 1 <= |target.y| := by
  by_contra hNeither
  push Not at hNeither
  have hxSquare : target.x ^ 2 < 1 := by
    have h := (sq_lt_sq₀ (abs_nonneg target.x) (by norm_num : (0 : Real) <= 1)).2
      hNeither.1
    simpa [sq_abs] using h
  have hySquare : target.y ^ 2 < 1 := by
    have h := (sq_lt_sq₀ (abs_nonneg target.y) (by norm_num : (0 : Real) <= 1)).2
      hNeither.2
    simpa [sq_abs] using h
  unfold onTargetCircle squaredRadius at hTarget
  nlinarith

theorem dominant_coordinate_ge_one {target : RealPlanePoint}
    (hTarget : onTargetCircle target) :
    (|target.y| <= |target.x| -> 1 <= |target.x|) /\
      (¬ |target.y| <= |target.x| -> 1 <= |target.y|) := by
  rcases target_has_unit_coordinate hTarget with hx | hy
  · constructor
    · intro _
      exact hx
    · intro hNot
      exact le_trans hx (le_of_lt (lt_of_not_ge hNot))
  · constructor
    · intro hDominant
      exact le_trans hy hDominant
    · intro _
      exact hy

theorem inwardRounded_abs_eq (m : Nat) (hm : 0 < m)
    (coordinate : Real) :
    |inwardRoundedCoordinate m coordinate| =
      (inwardOffset m coordinate : Real) / (m : Real) := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  have hQuotient :
      0 <= (inwardOffset m coordinate : Real) / (m : Real) := by positivity
  by_cases hSign : 0 <= coordinate
  · simp [inwardRoundedCoordinate, hSign, abs_of_nonneg hQuotient]
  · simp [inwardRoundedCoordinate, hSign, abs_of_nonneg hQuotient]

theorem inwardRounded_abs_le (m : Nat) (hm : 0 < m)
    (coordinate : Real) :
    |inwardRoundedCoordinate m coordinate| <= |coordinate| := by
  have hmReal : (0 : Real) < m := by exact_mod_cast hm
  rw [inwardRounded_abs_eq m hm coordinate]
  apply (div_le_iff₀ hmReal).2
  simpa [mul_comm] using inwardOffset_cast_le m coordinate

theorem inwardRounded_abs_gap_lt (m : Nat) (hm : 0 < m)
    (coordinate : Real) :
    |coordinate| - |inwardRoundedCoordinate m coordinate| < 1 / (m : Real) := by
  have hOrdered := inwardRounded_abs_le m hm coordinate
  have hReverseTriangle :=
    abs_abs_sub_abs_le_abs_sub coordinate (inwardRoundedCoordinate m coordinate)
  have hError := inwardRoundedCoordinate_error hm coordinate
  have hRewrite :
      |(|coordinate| - |inwardRoundedCoordinate m coordinate|)| =
        |coordinate| - |inwardRoundedCoordinate m coordinate| :=
    abs_of_nonneg (sub_nonneg.mpr hOrdered)
  rw [hRewrite] at hReverseTriangle
  exact lt_of_le_of_lt hReverseTriangle hError

theorem radial_bracket_affine_error
    (mScale a orthogonal rounded inside outside t : Real)
    (hm : 0 < mScale)
    (ha : 1 <= a)
    (hOrthogonal : 0 <= orthogonal)
    (hRounded : 0 <= rounded)
    (hRoundedLe : rounded <= orthogonal)
    (hRoundingGap : orthogonal - rounded < 1 / mScale)
    (hInsideNonneg : 0 <= inside)
    (hOutsideEq : outside = inside + 1 / mScale)
    (hInsideRadial : inside ^ 2 + rounded ^ 2 <= 2)
    (hOutsideRadial : 2 < outside ^ 2 + rounded ^ 2)
    (hTargetRadial : a ^ 2 + orthogonal ^ 2 = 2)
    (ht0 : 0 <= t) (ht1 : t <= 1) :
    |a - ((1 - t) * inside + t * outside)| <= 3 / mScale := by
  have hmInv : 0 < 1 / mScale := one_div_pos.mpr hm
  have ha0 : 0 <= a := le_trans (by norm_num) ha
  have hOutsideNonneg : 0 <= outside := by
    rw [hOutsideEq]
    positivity
  have hRoundedSquare : rounded ^ 2 <= orthogonal ^ 2 :=
    (sq_le_sq₀ hRounded hOrthogonal).2 hRoundedLe
  have hOutsideSquare : a ^ 2 < outside ^ 2 := by
    nlinarith
  have hOutsideGreater : a < outside :=
    (sq_lt_sq₀ ha0 hOutsideNonneg).1 hOutsideSquare
  have haSquare : 1 <= a ^ 2 := by
    have := (sq_le_sq₀ (by norm_num : (0 : Real) <= 1) ha0).2 ha
    norm_num at this ⊢
    exact this
  have hOrthogonalSquare : orthogonal ^ 2 <= 1 := by
    nlinarith
  have hOrthogonalLeOne : orthogonal <= 1 := by
    nlinarith [sq_nonneg (orthogonal - 1)]
  have hRoundedPlusOrthogonal : rounded + orthogonal <= 2 := by
    linarith
  have hSquareGapIdentity :
      orthogonal ^ 2 - rounded ^ 2 =
        (orthogonal - rounded) * (orthogonal + rounded) := by ring
  have hSquareGapBound :
      orthogonal ^ 2 - rounded ^ 2 <= 2 / mScale := by
    rw [hSquareGapIdentity]
    calc
      (orthogonal - rounded) * (orthogonal + rounded) <=
          (1 / mScale) * (orthogonal + rounded) :=
        mul_le_mul_of_nonneg_right (le_of_lt hRoundingGap)
          (add_nonneg hOrthogonal hRounded)
      _ <= (1 / mScale) * 2 :=
        mul_le_mul_of_nonneg_left
          (by linarith [hRoundedPlusOrthogonal]) (le_of_lt hmInv)
      _ = 2 / mScale := by ring
  have hInsideSquareGap :
      inside ^ 2 - a ^ 2 <= orthogonal ^ 2 - rounded ^ 2 := by
    nlinarith
  have hInsideUpper : inside - a <= 2 / mScale := by
    by_cases hIA : inside <= a
    · exact le_trans (sub_nonpos.mpr hIA) (le_of_lt (by positivity : 0 < 2 / mScale))
    · have hDifference : 0 <= inside - a := sub_nonneg.mpr (le_of_not_ge hIA)
      have hSum : 1 <= inside + a := by linarith
      have hProductLower :
          inside - a <= (inside - a) * (inside + a) := by
        nlinarith
      have hProductIdentity :
          (inside - a) * (inside + a) = inside ^ 2 - a ^ 2 := by ring
      rw [hProductIdentity] at hProductLower
      exact le_trans hProductLower (le_trans hInsideSquareGap hSquareGapBound)
  have hInsideLower : a - inside < 1 / mScale := by
    rw [hOutsideEq] at hOutsideGreater
    linarith
  have hAffine :
      (1 - t) * inside + t * outside = inside + t / mScale := by
    rw [hOutsideEq]
    ring
  have hStep0 : 0 <= t / mScale := by positivity
  have hStep1 : t / mScale <= 1 / mScale := by
    apply (div_le_div_iff_of_pos_right hm).2
    exact ht1
  have hAffineUpper :
      inside + t / mScale - a <= 3 / mScale := by
    calc
      inside + t / mScale - a = (inside - a) + t / mScale := by ring
      _ <= 2 / mScale + 1 / mScale := add_le_add hInsideUpper hStep1
      _ = 3 / mScale := by ring
  have hOneLeThree : 1 / mScale <= 3 / mScale := by
    apply (div_le_div_iff_of_pos_right hm).2
    norm_num
  have hAffineLower :
      a - (inside + t / mScale) <= 3 / mScale := by
    calc
      a - (inside + t / mScale) <= a - inside := by linarith
      _ <= 1 / mScale := le_of_lt hInsideLower
      _ <= 3 / mScale := hOneLeThree
  rw [hAffine, abs_le]
  exact ⟨by linarith, hAffineLower⟩

end
end DominantCoordinateMetricPrelude
end BoundaryOfSelf

#print axioms BoundaryOfSelf.DominantCoordinateMetricPrelude.target_has_unit_coordinate
#print axioms BoundaryOfSelf.DominantCoordinateMetricPrelude.dominant_coordinate_ge_one
#print axioms BoundaryOfSelf.DominantCoordinateMetricPrelude.inwardRounded_abs_gap_lt
#print axioms BoundaryOfSelf.DominantCoordinateMetricPrelude.radial_bracket_affine_error
