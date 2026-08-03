import InterpolatedBoundaryContour

namespace BoundaryOfSelf
namespace InterpolatedBoundaryContourAudit

open RationalBoundaryLimit
open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour

example {m : Nat} (e : CrossingEdge m) :
    0 < interpolationDenominator e /\
    interpolationNumerator e <= interpolationDenominator e := by
  exact ⟨interpolationDenominator_pos e,
    interpolationNumerator_le_denominator e⟩

example {m : Nat} (e : CrossingEdge m) :
    interpolationDenominator e * radialNumerator (innerPoint e) +
      interpolationNumerator e * interpolationDenominator e =
    interpolationDenominator e * thresholdNumerator m := by
  exact interpolation_hits_threshold e

example {m : Nat} (hm : 0 < m) (e : CrossingEdge m) :
    FractionLePositive (innerArcDistance hm e) (cellWidth m hm) /\
    FractionLePositive (outerArcDistance hm e) (cellWidth m hm) := by
  exact ⟨innerArcDistance_le_cellWidth hm e,
    outerArcDistance_le_cellWidth hm e⟩

example : forall epsilon : PositiveFraction, exists N : Nat,
    0 < N /\ forall (m : Nat) (hm : 0 < m), N <= m ->
      FractionLt (cellWidth m hm) epsilon /\
      forall e : CrossingEdge m,
        FractionLePositive (innerArcDistance hm e) (cellWidth m hm) /\
        FractionLePositive (outerArcDistance hm e) (cellWidth m hm) := by
  exact interpolated_contour_mesh_limit

#print axioms interpolation_hits_threshold
#print axioms innerArcDistance_le_cellWidth
#print axioms outerArcDistance_le_cellWidth
#print axioms interpolated_contour_mesh_limit

end InterpolatedBoundaryContourAudit
end BoundaryOfSelf
