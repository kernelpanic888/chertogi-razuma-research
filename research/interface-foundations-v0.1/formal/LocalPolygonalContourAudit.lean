import LocalPolygonalContour

namespace BoundaryOfSelf
namespace LocalPolygonalContourAudit

open UniformRadialBoundaryFamily
open InterpolatedBoundaryContour
open LocalPolygonalContour

example {m : Nat} (c : GridCell m) :
    radialNumerator (southWest c) + radialNumerator (northEast c) =
    radialNumerator (southEast c) + radialNumerator (northWest c) := by
  exact cell_parallelogram c

example {m : Nat} (c : GridCell m) (h : ActiveCell c) :
    (crossingSides c).length = 2 := by
  exact activeCell_has_exactly_two_sides c h

example {m : Nat} (segment : LocalContourSegment m) :
    (segmentSides segment).length = 2 := by
  exact segment_has_exactly_two_vertices segment

example {m : Nat} (e : CrossingEdge m) :
    (interpolationParameter (reverseEdge e)).numerator =
      (interpolationParameter e).numerator /\
    (interpolationParameter (reverseEdge e)).denominator =
      (interpolationParameter e).denominator := by
  exact reverse_parameter_coordinates e

#print axioms cell_parallelogram
#print axioms activeCell_has_exactly_two_sides
#print axioms segment_has_exactly_two_vertices
#print axioms reverse_parameter_coordinates

end LocalPolygonalContourAudit
end BoundaryOfSelf
