import UniformRadialBoundaryFamily

namespace BoundaryOfSelf
namespace UniformRadialBoundaryFamilyAudit

open RationalBoundaryLimit
open RefinedCurvedBoundaryGrid
open UniformRadialBoundaryFamily

example (m : Nat) : radialGridSide m = 2 * (2 * m) + 1 := by
  exact radialGridSide_odd_shape m

example : radialGridSide 4 = 17 := by
  exact scale_four_side

example (p : FineGridPoint) :
    radialNumerator (fineSample p) = fineScalarNumerator p := by
  exact fineSample_numerator p

example {m : Nat} (hm : 0 < m) (p q : GridSample m)
    (ha : UnitAdjacent p q) (hc : Crosses p q) :
    WithinFieldBand p (5 * m) /\ WithinFieldBand q (5 * m) := by
  exact crossing_within_five_cell_band hm p q ha hc

example : forall epsilon : PositiveFraction, exists N : Nat,
    0 < N /\ forall (m : Nat) (hm : 0 < m), N <= m ->
      FractionLt (normalizedBandWidth m hm) epsilon := by
  exact normalized_band_limit

#print axioms adjacent_numerator_gap
#print axioms crossing_within_five_cell_band
#print axioms normalized_band_limit
#print axioms fineSample_numerator

end UniformRadialBoundaryFamilyAudit
end BoundaryOfSelf
