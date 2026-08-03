import ThresholdCutBond

namespace BoundaryOfSelf
namespace ThresholdCutBondAudit

open UniformRadialBoundaryFamily
open FiniteGridReachability
open ThresholdCutBond

example {m : Nat} (insidePoint outsidePoint : GridSample m)
    (hInside : Inside insidePoint) (hOutside : ¬ Inside outsidePoint) :
    ¬ StepReachable NoncrossingStep insidePoint outsidePoint := by
  exact noncrossing_separates_sides insidePoint outsidePoint hInside hOutside

example {m : Nat} (hm : 0 < m) (bridge : OrientedCrossing m)
    (start finish : GridSample m)
    (hStart : Inside start) (hFinish : ¬ Inside finish) :
    StepReachable (BridgeStep bridge) start finish := by
  exact one_crossing_reconnects_sides hm bridge start finish hStart hFinish

example {m : Nat} (hm : 0 < m) : ThresholdCutIsBond m := by
  exact radialThresholdCut_isBond hm

#print axioms noncrossingReachable_inside_iff
#print axioms noncrossing_separates_sides
#print axioms crossing_is_orientable
#print axioms orientCrossing
#print axioms orientCrossing_spec
#print axioms one_crossing_reconnects_sides
#print axioms raw_crossing_reconnects_sides
#print axioms radialThresholdCut_isBond

end ThresholdCutBondAudit
end BoundaryOfSelf
