import GridPhysicalCoordinateAdapter

namespace BoundaryOfSelf
namespace GridPhysicalCoordinateAdapterAudit

open GridPhysicalCoordinateAdapter

#check physicalX
#check physicalY
#check physicalPoint
#check physicalPoint_squaredRadius
#check physicalPoint_inside
#check physicalPoint_outside
#check physicalX_step_right
#check physicalX_step_left
#check physicalY_step_up
#check physicalY_step_down
#check physical_targetAxis
#check physicalY_of_targetAxis
#check physicalX_of_swappedTargetAxis

#print axioms physicalPoint_squaredRadius
#print axioms physicalPoint_inside
#print axioms physicalPoint_outside
#print axioms physical_targetAxis

end GridPhysicalCoordinateAdapterAudit
end BoundaryOfSelf
