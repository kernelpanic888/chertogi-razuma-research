import ConcreteRadialContourTraversal

namespace BoundaryOfSelf
namespace ConcreteRadialContourTraversalAudit

open LocalPolygonalContour
open FiniteAlternatingCycleKernel
open ConcreteRadialContourTraversal

example {m : Nat} (a : ContourState m) :
    ExistsUniqueValue (LocalPartner a) := by
  exact localPartner_existsUnique a

example {m : Nat} (hm : 0 < m) (a : ContourState m) :
    ExistsUniqueValue (SharedPartner a) := by
  exact sharedPartner_existsUnique hm a

example {m : Nat} (hm : 0 < m) (state : ContourState m) :
    exists period : Nat, 0 < period /\
      iterate
        (successor (localInvolution (m := m)) (sharedInvolution hm))
        period state = state := by
  exact every_radial_contour_state_has_closed_cycle hm state

#print axioms localPartner_existsUnique
#print axioms sharedPartner_existsUnique
#print axioms localInvolution
#print axioms sharedInvolution
#print axioms contourStateCover_covers
#print axioms every_radial_contour_state_has_closed_cycle

end ConcreteRadialContourTraversalAudit
end BoundaryOfSelf
