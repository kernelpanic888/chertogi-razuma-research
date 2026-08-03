import GlobalContourZeroBoundary

namespace BoundaryOfSelf
namespace GlobalContourZeroBoundaryAudit

open GlobalContourIncidence
open GlobalContourZeroBoundary

example {m : Nat} (hm : 0 < m) (e : HorizontalGridEdge m)
    (h : HorizontalCrosses e) : ExactlyTwo (HorizontalIncident e) := by
  exact horizontal_exactly_two_incidences hm e h

example {m : Nat} (hm : 0 < m) (e : VerticalGridEdge m)
    (h : VerticalCrosses e) : ExactlyTwo (VerticalIncident e) := by
  exact vertical_exactly_two_incidences hm e h

example {m : Nat} (hm : 0 < m) : ModTwoBoundaryZero m := by
  exact radialContour_modTwoBoundaryZero hm

example : 2 % 2 = 0 := by
  exact exact_degree_two_is_zero_mod_two

#print axioms horizontal_representation_classification
#print axioms vertical_representation_classification
#print axioms horizontal_exactly_two_incidences
#print axioms vertical_exactly_two_incidences
#print axioms radialContour_modTwoBoundaryZero

end GlobalContourZeroBoundaryAudit
end BoundaryOfSelf
