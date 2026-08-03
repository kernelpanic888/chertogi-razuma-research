import ConnectednessC01Adapter

namespace BoundaryOfSelf
namespace C01ReachabilityTopology

open ConnectednessC01Adapter

/-!
IF-BS-C02 constructs a Kuratowski closure topology from C-01 reachability.
The space consists only of admissible states. The closure of a region contains
exactly the states reachable from some state in that region.
-/

abbrev AdmissibleState {State : Type} (carrier : C01Carrier State) :=
  { state : State // carrier.admissible state }

def reachableClosure {State : Type} (carrier : C01Carrier State)
    (region : Region (AdmissibleState carrier)) :
    Region (AdmissibleState carrier) :=
  fun target => exists source,
    region source /\ C01Reachable carrier source.val target.val

theorem subset_reachableClosure {State : Type}
    (carrier : C01Carrier State)
    (region : Region (AdmissibleState carrier)) :
    Subset region (reachableClosure carrier region) := by
  intro point has
  exact ⟨point, has, C01Reachable.refl point.val point.property⟩

theorem reachableClosure_mono {State : Type}
    (carrier : C01Carrier State)
    {left right : Region (AdmissibleState carrier)}
    (included : Subset left right) :
    Subset (reachableClosure carrier left)
      (reachableClosure carrier right) := by
  intro target has
  rcases has with ⟨source, source_has, path⟩
  exact ⟨source, included source source_has, path⟩

theorem reachableClosure_idempotent {State : Type}
    (carrier : C01Carrier State)
    (region : Region (AdmissibleState carrier)) :
    reachableClosure carrier (reachableClosure carrier region) =
      reachableClosure carrier region := by
  funext target
  apply propext
  constructor
  · intro has
    rcases has with ⟨middle, ⟨source, source_has, first⟩, second⟩
    exact ⟨source, source_has,
      C01Reachable.trans source.val middle.val target.val first second⟩
  · intro has
    exact ⟨target, has,
      C01Reachable.refl target.val target.property⟩

theorem reachableClosure_empty {State : Type}
    (carrier : C01Carrier State) :
    reachableClosure carrier (fun _ => False) = (fun _ => False) := by
  funext target
  apply propext
  constructor
  · intro has
    rcases has with ⟨source, impossible, _⟩
    exact impossible
  · intro impossible
    exact False.elim impossible

theorem reachableClosure_union {State : Type}
    (carrier : C01Carrier State)
    (left right : Region (AdmissibleState carrier)) :
    reachableClosure carrier (Union left right) =
      Union (reachableClosure carrier left)
        (reachableClosure carrier right) := by
  funext target
  apply propext
  constructor
  · intro has
    rcases has with ⟨source, source_has, path⟩
    rcases source_has with left_has | right_has
    · exact Or.inl ⟨source, left_has, path⟩
    · exact Or.inr ⟨source, right_has, path⟩
  · intro has
    rcases has with left_has | right_has
    · rcases left_has with ⟨source, source_has, path⟩
      exact ⟨source, Or.inl source_has, path⟩
    · rcases right_has with ⟨source, source_has, path⟩
      exact ⟨source, Or.inr source_has, path⟩

def reachabilityTopology {State : Type}
    (carrier : C01Carrier State) :
    ClosureTopology (AdmissibleState carrier) where
  closure := reachableClosure carrier
  subset_closure := subset_reachableClosure carrier
  closure_mono := reachableClosure_mono carrier
  closure_idempotent := reachableClosure_idempotent carrier
  closure_empty := reachableClosure_empty carrier
  closure_union := reachableClosure_union carrier

theorem c01Connected_implies_isConnected {State : Type}
    (carrier : C01Carrier State)
    (connected : C01Connected carrier) :
    IsConnected (reachabilityTopology carrier) := by
  intro region closed _open
  classical
  by_cases inhabited_region : exists point, region point
  · right
    intro target
    rcases inhabited_region with ⟨source, source_has⟩
    have path : C01Reachable carrier source.val target.val :=
      connected source.val target.val source.property target.property
    exact closed target ⟨source, source_has, path⟩
  · left
    intro point point_has
    exact inhabited_region ⟨point, point_has⟩

theorem properRegion_hasBoundary_via_c01 {State : Type}
    (carrier : C01Carrier State)
    (connected : C01Connected carrier)
    (region : Region (AdmissibleState carrier))
    (proper : ProperRegion region) :
    BoundaryNonempty (reachabilityTopology carrier) region := by
  exact properRegion_hasTopologicalBoundary
    (reachabilityTopology carrier)
    (c01Connected_implies_isConnected carrier connected)
    region proper

theorem topologicalSelf_hasBoundary_via_c01 {State : Type}
    (carrier : C01Carrier State)
    (connected : C01Connected carrier)
    (point : AdmissibleState carrier)
    (region : Region (AdmissibleState carrier))
    (self_record : TopologicalSelfRecord
      (reachabilityTopology carrier) point region) :
    BoundaryNonempty (reachabilityTopology carrier) region := by
  exact topologicalSelf_hasBoundary
    (reachabilityTopology carrier)
    (c01Connected_implies_isConnected carrier connected)
    point region self_record

def insideReachabilityTopology (m : Nat) :=
  reachabilityTopology (insideCarrier m)

def outsideReachabilityTopology (m : Nat) :=
  reachabilityTopology (outsideCarrier m)

theorem insideReachabilityTopology_connected (m : Nat) :
    IsConnected (insideReachabilityTopology m) := by
  exact c01Connected_implies_isConnected (insideCarrier m)
    (insideCarrier_connected m)

theorem outsideReachabilityTopology_connected (m : Nat) (hm : 0 < m) :
    IsConnected (outsideReachabilityTopology m) := by
  exact c01Connected_implies_isConnected (outsideCarrier m)
    (outsideCarrier_connected m hm)

end C01ReachabilityTopology
end BoundaryOfSelf

#print axioms BoundaryOfSelf.C01ReachabilityTopology.reachableClosure_idempotent
#print axioms BoundaryOfSelf.C01ReachabilityTopology.reachabilityTopology
#print axioms BoundaryOfSelf.C01ReachabilityTopology.c01Connected_implies_isConnected
#print axioms BoundaryOfSelf.C01ReachabilityTopology.properRegion_hasBoundary_via_c01
#print axioms BoundaryOfSelf.C01ReachabilityTopology.insideReachabilityTopology_connected
#print axioms BoundaryOfSelf.C01ReachabilityTopology.outsideReachabilityTopology_connected
