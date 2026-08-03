import FiniteGridReachability

namespace BoundaryOfSelf
namespace ConnectednessC01Adapter

open UniformRadialBoundaryFamily
open FiniteGridReachability

/-!
IF-BS-C01 separates two meanings of connectedness.

The C-01 reader supplies a context-indexed carrier of admissible states and
transitions. IF-BS-01 uses topological connectedness of a closure space. The
definitions below make the first notion precise, instantiate it for the radial
grid proved connected in IF-BS-18, and leave the transport to the second notion
as an explicit obligation rather than an implicit change of meaning.
-/

structure C01Carrier (State : Type) where
  admissible : State -> Prop
  transition : State -> State -> Prop

inductive C01Reachable {State : Type}
    (carrier : C01Carrier State) : State -> State -> Prop where
  | refl (state : State) (has : carrier.admissible state) :
      C01Reachable carrier state state
  | step (source target : State)
      (source_has : carrier.admissible source)
      (target_has : carrier.admissible target)
      (moves : carrier.transition source target) :
      C01Reachable carrier source target
  | trans (source middle target : State)
      (first : C01Reachable carrier source middle)
      (second : C01Reachable carrier middle target) :
      C01Reachable carrier source target

def C01Connected {State : Type} (carrier : C01Carrier State) : Prop :=
  forall source target,
    carrier.admissible source ->
    carrier.admissible target ->
    C01Reachable carrier source target

def radialCarrier {m : Nat}
    (P : GridSample m -> Prop) : C01Carrier (GridSample m) where
  admissible := P
  transition := fun source target =>
    P source /\ P target /\ UnitAdjacent source target

theorem gridReachable_to_c01Reachable {m : Nat}
    {P : GridSample m -> Prop} {source target : GridSample m}
    (path : GridReachable P source target) :
    C01Reachable (radialCarrier P) source target := by
  induction path with
  | refl state has =>
      exact C01Reachable.refl state has
  | edge source target source_has target_has adjacent =>
      exact C01Reachable.step source target source_has target_has
        <| And.intro source_has <| And.intro target_has adjacent
  | trans source middle target first second first_ih second_ih =>
      exact C01Reachable.trans source middle target first_ih second_ih

def insideCarrier (m : Nat) : C01Carrier (GridSample m) :=
  radialCarrier Inside

def outsideCarrier (m : Nat) : C01Carrier (GridSample m) :=
  radialCarrier (fun point => Not (Inside point))

theorem insideCarrier_connected (m : Nat) :
    C01Connected (insideCarrier m) := by
  intro source target source_has target_has
  exact gridReachable_to_c01Reachable
    (any_two_inside_samples_connected source target source_has target_has)

theorem outsideCarrier_connected (m : Nat) (hm : 0 < m) :
    C01Connected (outsideCarrier m) := by
  intro source target source_has target_has
  exact gridReachable_to_c01Reachable
    (any_two_outside_samples_connected hm source target source_has target_has)

structure C01TopologicalRealization
    (State X : Type) (carrier : C01Carrier State)
    (topology : ClosureTopology X) where
  realize : State -> X
  connectedness_transport : C01Connected carrier -> IsConnected topology

theorem topologicalSelf_hasBoundary_via_c01
    {State X : Type} {carrier : C01Carrier State}
    {topology : ClosureTopology X}
    (realization : C01TopologicalRealization State X carrier topology)
    (carrier_connected : C01Connected carrier)
    (point : X) (region : Region X)
    (self_record : TopologicalSelfRecord topology point region) :
    BoundaryNonempty topology region := by
  exact topologicalSelf_hasBoundary topology
    (realization.connectedness_transport carrier_connected)
    point region self_record

end ConnectednessC01Adapter
end BoundaryOfSelf

#print axioms BoundaryOfSelf.ConnectednessC01Adapter.gridReachable_to_c01Reachable
#print axioms BoundaryOfSelf.ConnectednessC01Adapter.insideCarrier_connected
#print axioms BoundaryOfSelf.ConnectednessC01Adapter.outsideCarrier_connected
#print axioms BoundaryOfSelf.ConnectednessC01Adapter.topologicalSelf_hasBoundary_via_c01
