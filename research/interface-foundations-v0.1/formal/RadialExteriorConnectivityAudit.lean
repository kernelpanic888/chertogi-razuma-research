import RadialExteriorConnectivity

namespace BoundaryOfSelf
namespace RadialExteriorConnectivityAudit

open UniformRadialBoundaryFamily
open RadialOrthogonalConvexity
open RadialExteriorConnectivity

example {m : Nat} (start middle : GridSample m)
    (hBetween : BetweenNat start.x middle.x (outwardX start)) :
    xOffset start <= xOffset middle := by
  exact xOffset_le_on_outward_segment start middle hBetween

example {m : Nat} (hm : 0 < m) (start : GridSample m)
    (hOutside : ¬ Inside start) :
    exists xFrame bottomFrame : GridSample m,
      HorizontalSegmentOutside start xFrame /\
      VerticalSegmentOutside xFrame bottomFrame /\
      HorizontalSegmentOutside bottomFrame (originFrameCorner m) := by
  exact radial_outside_reaches_common_frame_corner hm start hOutside

#print axioms xOffset_le_on_outward_segment
#print axioms outward_horizontal_segment_outside
#print axioms vertical_outer_frame_segment_outside
#print axioms bottom_outer_frame_segment_outside
#print axioms radial_outside_reaches_common_frame_corner

end RadialExteriorConnectivityAudit
end BoundaryOfSelf
