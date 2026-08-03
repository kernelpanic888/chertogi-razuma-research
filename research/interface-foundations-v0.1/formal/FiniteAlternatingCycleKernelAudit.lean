import FiniteAlternatingCycleKernel

namespace BoundaryOfSelf
namespace FiniteAlternatingCycleKernelAudit

open FiniteAlternatingCycleKernel

example {alpha : Type}
    (localMate sharedMate : FixedPointFreeInvolution alpha)
    (x : alpha) :
    predecessor localMate sharedMate (successor localMate sharedMate x) = x /\
    successor localMate sharedMate (predecessor localMate sharedMate x) = x := by
  exact ⟨predecessor_successor localMate sharedMate x,
    successor_predecessor localMate sharedMate x⟩

example {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (cover : List alpha) (hCover : forall x : alpha, x ∈ cover)
    (f : alpha -> alpha) (x : alpha) :
    exists i j : Nat, i < j /\ j < cover.length + 1 /\
      iterate f i x = iterate f j x := by
  exact finite_orbit_has_repeat cover hCover f x

example {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (traversal : FiniteAlternatingTraversal alpha) (x : alpha) :
    exists period : Nat, 0 < period /\
      iterate (successor traversal.localMate traversal.sharedMate) period x = x := by
  exact every_state_has_closed_cycle traversal x

#print axioms nodup_length_le_of_cover
#print axioms finite_orbit_has_repeat
#print axioms predecessor_successor
#print axioms repeat_of_inverse_has_positive_period
#print axioms every_state_has_closed_cycle

end FiniteAlternatingCycleKernelAudit
end BoundaryOfSelf
