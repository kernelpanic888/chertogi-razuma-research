import RadialOrthogonalConvexity

namespace BoundaryOfSelf
namespace RadialOrthogonalConvexityAudit

open UniformRadialBoundaryFamily
open RadialOrthogonalConvexity

example {m : Nat} (near far : GridSample m)
    (hx : xOffset near <= xOffset far)
    (hy : yOffset near <= yOffset far)
    (hFarInside : Inside far) : Inside near := by
  exact inside_of_offsets_le near far hx hy hFarInside

example {m : Nat} (left right middle : GridSample m)
    (hRow : left.y = right.y) (hMiddleRow : middle.y = left.y)
    (hBetween : BetweenNat left.x middle.x right.x)
    (hLeftInside : Inside left) (hRightInside : Inside right) :
    Inside middle := by
  exact row_inside_interval left right middle hRow hMiddleRow hBetween
    hLeftInside hRightInside

example {m : Nat} (start : GridSample m) (hInside : Inside start) :
    exists corner : GridSample m,
      HorizontalSegmentInside start corner /\
      VerticalSegmentInside corner (centerSample m) := by
  exact radial_inside_is_orthogonally_star_connected start hInside

#print axioms radialNumerator_le_of_offsets_le
#print axioms row_inside_interval
#print axioms column_inside_interval
#print axioms centerSample_inside
#print axioms radial_inside_is_orthogonally_star_connected

end RadialOrthogonalConvexityAudit
end BoundaryOfSelf
