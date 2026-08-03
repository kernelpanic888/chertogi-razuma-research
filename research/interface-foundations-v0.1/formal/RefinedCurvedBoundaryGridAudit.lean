import RefinedCurvedBoundaryGrid

namespace BoundaryOfSelf
namespace RefinedCurvedBoundaryGridAudit

open CurvedBoundaryGrid
open RefinedCurvedBoundaryGrid

example : allFineGridPoints.length = 289 :=
  fine_grid_has_two_hundred_eighty_nine_points

example : allFineGridEdges.length = 544 :=
  fine_grid_has_five_hundred_forty_four_edges

example : fineInsidePoints.length = 101 :=
  fine_radial_region_has_one_hundred_one_nodes

example : fineContourEdges.length = 44 :=
  fine_contour_has_forty_four_edges

example (p : GridPoint) :
    fineScalarNumerator (embedPoint p) = 16 * scalarField p :=
  fineScalar_on_embedded_coarse p

example (p : GridPoint) :
    fineInsideFlag (embedPoint p) = insideFlag p :=
  fineInside_on_embedded_coarse p

example (p : GridPoint) : coarsenPoint (embedPoint p) = p :=
  coarsen_embedPoint p

example {e : FineGridEdge} (h : e ∈ fineContourEdges) :
    nearCoarseContour e.source = true ∧
      nearCoarseContour e.target = true :=
  fineContourEdge_localizes_within_one_coarse_cell h

example (e : FineGridEdge) :
    e ∈ fineContourEdges ↔
      e ∈ allFineGridEdges ∧ fineCrossesFlag e = true :=
  reportedFineEdge_iff_gridCrossing e

end RefinedCurvedBoundaryGridAudit
end BoundaryOfSelf

#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fine_grid_has_two_hundred_eighty_nine_points
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fine_contour_has_forty_four_edges
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fineScalar_on_embedded_coarse
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fineInside_on_embedded_coarse
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.coarsen_embedPoint
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fineAxis_coarsens_within_one_cell
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.fineContourEdge_localizes_within_one_coarse_cell
#print axioms BoundaryOfSelf.RefinedCurvedBoundaryGrid.reportedFineEdge_iff_gridCrossing
