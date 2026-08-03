import CurvedBoundaryGrid

namespace BoundaryOfSelf
namespace CurvedBoundaryGridAudit

open CurvedBoundaryGrid

example : allGridPoints.length = 25 :=
  grid_has_twenty_five_points

example : allGridEdges.length = 40 :=
  grid_has_forty_edges

example : insidePoints.length = 9 :=
  radial_region_has_nine_nodes

example : contourEdges.length = 12 :=
  contour_has_twelve_edges

example {e : GridEdge} (h : e ∈ contourEdges) :
    adjacentFlag e = true ∧ crossesFlag e = true :=
  contourEdge_isAdjacent_and_crosses h

example (e : GridEdge) :
    e ∈ contourEdges ↔ e ∈ allGridEdges ∧ crossesFlag e = true :=
  reportedEdge_iff_gridCrossing e

end CurvedBoundaryGridAudit
end BoundaryOfSelf

#print axioms BoundaryOfSelf.CurvedBoundaryGrid.grid_has_twenty_five_points
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.grid_has_forty_edges
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.radial_region_has_nine_nodes
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.contour_has_twelve_edges
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.contourEdge_isAdjacent_and_crosses
#print axioms BoundaryOfSelf.CurvedBoundaryGrid.reportedEdge_iff_gridCrossing
