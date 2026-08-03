import FiniteGridReachability

namespace BoundaryOfSelf
namespace FiniteGridReachabilityAudit

open UniformRadialBoundaryFamily
open RadialOrthogonalConvexity
open RadialExteriorConnectivity
open FiniteGridReachability

example {m : Nat} (left right : GridSample m)
    (hLeft : Inside left) (hRight : Inside right) :
    GridReachable Inside left right := by
  exact any_two_inside_samples_connected left right hLeft hRight

example {m : Nat} (hm : 0 < m) (left right : GridSample m)
    (hLeft : ¬ Inside left) (hRight : ¬ Inside right) :
    GridReachable (fun point => ¬ Inside point) left right := by
  exact any_two_outside_samples_connected hm left right hLeft hRight

#print axioms horizontal_segment_reachable
#print axioms vertical_segment_reachable
#print axioms every_inside_sample_reaches_center
#print axioms every_outside_sample_reaches_frame_corner
#print axioms any_two_inside_samples_connected
#print axioms any_two_outside_samples_connected

end FiniteGridReachabilityAudit
end BoundaryOfSelf
