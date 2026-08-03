import FiniteRadialBoundaryTheorem

namespace BoundaryOfSelf
namespace InterpolatedCurvatureResidual

open RationalBoundaryLimit
open RefinedCurvedBoundaryGrid
open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour

/-!
IF-BS-22A isolates the exact quadratic correction of a linearly interpolated
unit-grid edge. If the interpolation parameter is n/d, the normalized
curvature residual is n(d-n)/(d^2 m^2). This module proves a uniform 1/m^2
upper bound and its epsilon limit. The later planar module must connect this
algebraic correction to embedded segment coordinates and Hausdorff distance.
-/

def squaredCellWidth (m : Nat) (hm : 0 < m) : PositiveFraction where
  numerator := 1
  denominator := m * m
  numerator_pos := by omega
  denominator_pos := Nat.mul_pos hm hm

def curvatureResidualNumerator {m : Nat} (edge : CrossingEdge m) : Nat :=
  interpolationNumerator edge *
    (interpolationDenominator edge - interpolationNumerator edge)

def curvatureResidualDenominator {m : Nat} (hm : 0 < m)
    (edge : CrossingEdge m) : Nat :=
  interpolationDenominator edge * interpolationDenominator edge * (m * m)

theorem curvatureResidualDenominator_pos {m : Nat} (hm : 0 < m)
    (edge : CrossingEdge m) :
    0 < curvatureResidualDenominator hm edge := by
  unfold curvatureResidualDenominator
  exact Nat.mul_pos
    (Nat.mul_pos (interpolationDenominator_pos edge)
      (interpolationDenominator_pos edge))
    (Nat.mul_pos hm hm)

def curvatureResidual {m : Nat} (hm : 0 < m)
    (edge : CrossingEdge m) : NonnegativeFraction where
  numerator := curvatureResidualNumerator edge
  denominator := curvatureResidualDenominator hm edge
  denominator_pos := curvatureResidualDenominator_pos hm edge

theorem splitProduct_le_square (numerator denominator : Nat)
    (bounded : numerator <= denominator) :
    numerator * (denominator - numerator) <= denominator * denominator := by
  exact Nat.mul_le_mul bounded (Nat.sub_le denominator numerator)

theorem curvatureResidual_le_squaredCellWidth {m : Nat} (hm : 0 < m)
    (edge : CrossingEdge m) :
    FractionLePositive (curvatureResidual hm edge)
      (squaredCellWidth m hm) := by
  have core := splitProduct_le_square
    (interpolationNumerator edge) (interpolationDenominator edge)
    (interpolationNumerator_le_denominator edge)
  change
    curvatureResidualNumerator edge * (m * m) <=
      1 * curvatureResidualDenominator hm edge
  simp only [Nat.one_mul]
  unfold curvatureResidualNumerator curvatureResidualDenominator
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (m * m) core

theorem squared_cell_width_limit :
    forall epsilon : PositiveFraction, exists N : Nat,
      0 < N /\ forall (m : Nat) (hm : 0 < m), N <= m ->
        FractionLt (squaredCellWidth m hm) epsilon := by
  intro epsilon
  let N := epsilon.denominator + 1
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    omega
  · intro m hm hNm
    have denominator_lt_m : epsilon.denominator < m := by
      dsimp [N] at hNm
      omega
    have one_le_m : 1 <= m := hm
    have m_le_square : m <= m * m := by
      have scaled := Nat.mul_le_mul_left m one_le_m
      simpa using scaled
    have one_le_numerator : 1 <= epsilon.numerator :=
      epsilon.numerator_pos
    have square_le_scaled : m * m <= epsilon.numerator * (m * m) := by
      have scaled := Nat.mul_le_mul_right (m * m) one_le_numerator
      simpa using scaled
    unfold FractionLt squaredCellWidth
    simp only [Nat.one_mul]
    exact Nat.lt_of_lt_of_le denominator_lt_m
      (Nat.le_trans m_le_square square_le_scaled)

theorem interpolated_curvature_residual_limit :
    forall epsilon : PositiveFraction, exists N : Nat,
      0 < N /\ forall (m : Nat) (hm : 0 < m), N <= m ->
        FractionLt (squaredCellWidth m hm) epsilon /\
        forall edge : CrossingEdge m,
          FractionLePositive (curvatureResidual hm edge)
            (squaredCellWidth m hm) := by
  intro epsilon
  rcases squared_cell_width_limit epsilon with ⟨N, hN, hLimit⟩
  refine ⟨N, hN, ?_⟩
  intro m hm hNm
  exact ⟨hLimit m hm hNm,
    fun edge => curvatureResidual_le_squaredCellWidth hm edge⟩

structure InterpolatedEdgeRefinementCertificate (m : Nat) (hm : 0 < m) where
  mesh_width : PositiveFraction := cellWidth m hm
  squared_mesh_width : PositiveFraction := squaredCellWidth m hm
  every_inner_arc_bounded : forall edge : CrossingEdge m,
    FractionLePositive (innerArcDistance hm edge) mesh_width
  every_outer_arc_bounded : forall edge : CrossingEdge m,
    FractionLePositive (outerArcDistance hm edge) mesh_width
  every_curvature_residual_bounded : forall edge : CrossingEdge m,
    FractionLePositive (curvatureResidual hm edge) squared_mesh_width

def interpolatedEdgeRefinementCertificate {m : Nat} (hm : 0 < m) :
    InterpolatedEdgeRefinementCertificate m hm where
  every_inner_arc_bounded := innerArcDistance_le_cellWidth hm
  every_outer_arc_bounded := outerArcDistance_le_cellWidth hm
  every_curvature_residual_bounded :=
    curvatureResidual_le_squaredCellWidth hm

end InterpolatedCurvatureResidual
end BoundaryOfSelf

#print axioms BoundaryOfSelf.InterpolatedCurvatureResidual.splitProduct_le_square
#print axioms BoundaryOfSelf.InterpolatedCurvatureResidual.curvatureResidual_le_squaredCellWidth
#print axioms BoundaryOfSelf.InterpolatedCurvatureResidual.squared_cell_width_limit
#print axioms BoundaryOfSelf.InterpolatedCurvatureResidual.interpolated_curvature_residual_limit
#print axioms BoundaryOfSelf.InterpolatedCurvatureResidual.interpolatedEdgeRefinementCertificate
