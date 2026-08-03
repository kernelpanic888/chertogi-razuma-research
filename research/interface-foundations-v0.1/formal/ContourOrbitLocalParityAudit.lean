import ContourOrbitLocalParity

namespace BoundaryOfSelf
namespace ContourOrbitLocalParityAudit

open ContourOrbitLocalParity

#check contourLocalMate
#check contourSharedMate
#check contourSuccessor
#check contourPredecessor
#check SameContourOrbit
#check EdgeMarkedByOrbit
#check edgeMarked_localMate
#check SideMarkedByOrbit
#check all_crossing_sides_marked_of_one
#check cellSideMarks_zero_or_two
#check sideMarkBool
#check cellSideMark_even

#print axioms edgeMarked_localMate
#print axioms all_crossing_sides_marked_of_one
#print axioms cellSideMarks_zero_or_two
#print axioms exactlyTwo_cellSide_parity
#print axioms cellSideMark_even

end ContourOrbitLocalParityAudit
end BoundaryOfSelf
