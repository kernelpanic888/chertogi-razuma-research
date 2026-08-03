import BoundarySeparationInvariant

namespace BoundaryOfSelf
namespace AbstractBoundaryApproximation

noncomputable section

open Filter
open StandardHausdorffMetricBridge
open ConcreteRadialContourTraversal
open CompactHausdorffAttainment
open BoundarySeparationInvariant

universe u

variable {X : Type u} [PseudoMetricSpace X]

/-- Side labels are stable when every point has exactly one of the three roles:
inside, interface, or outside. -/
structure SideLabelInvariant
    (inside interface outside : Set X) : Prop where
  inside_interface_disjoint : Disjoint inside interface
  interface_outside_disjoint : Disjoint interface outside
  inside_outside_disjoint : Disjoint inside outside
  exhaustive : forall point, point ∈ inside ∨ point ∈ interface ∨ point ∈ outside

/-- The topological data needed before any computable contour is introduced. -/
structure BoundaryModel (X : Type u) [PseudoMetricSpace X] where
  inside : Set X
  interface : Set X
  outside : Set X
  proper_inside : ProperRegion (fun point => point ∈ inside)
  interface_nonempty : interface.Nonempty
  outside_nonempty : outside.Nonempty
  labels : SideLabelInvariant inside interface outside
  interface_is_frontier : frontier inside = interface

/-- A genuine computable approximation family. Compact nonempty carriers prevent
the real Hausdorff distance from hiding an infinite extended distance. -/
structure InterfaceApproximation (target : Set X) where
  carrier : Nat → Set X
  envelope : Nat → Real
  target_nonempty : target.Nonempty
  target_compact : IsCompact target
  carrier_nonempty : forall n, (carrier n).Nonempty
  carrier_compact : forall n, IsCompact (carrier n)
  hausdorff_le : forall n, Metric.hausdorffDist (carrier n) target <= envelope n
  envelope_tendsto_zero : Tendsto envelope atTop (nhds 0)

theorem InterfaceApproximation.hausdorffEDist_ne_top
    {target : Set X} (approximation : InterfaceApproximation target) (n : Nat) :
    Metric.hausdorffEDist (approximation.carrier n) target ≠ ⊤ := by
  exact Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    (approximation.carrier_nonempty n) approximation.target_nonempty
    (approximation.carrier_compact n).isBounded
    approximation.target_compact.isBounded

theorem InterfaceApproximation.hausdorff_tendsto_zero
    {target : Set X} (approximation : InterfaceApproximation target) :
    Tendsto
      (fun n => Metric.hausdorffDist (approximation.carrier n) target)
      atTop (nhds 0) := by
  exact squeeze_zero
    (fun _ => Metric.hausdorffDist_nonneg)
    approximation.hausdorff_le
    approximation.envelope_tendsto_zero

/-- The minimum bridge: topological identity plus a genuine computable family. -/
structure ComputableBoundaryModel (X : Type u) [PseudoMetricSpace X]
    extends BoundaryModel X where
  approximation : InterfaceApproximation interface

theorem ComputableBoundaryModel.converges_to_actual_frontier
    (model : ComputableBoundaryModel X) :
    Tendsto
      (fun n => Metric.hausdorffDist
        (model.approximation.carrier n) (frontier model.inside))
      atTop (nhds 0) := by
  rw [model.interface_is_frontier]
  exact model.approximation.hausdorff_tendsto_zero

def radialBoundaryModel : BoundaryModel AmbientPlane where
  inside := identityRegion
  interface := identityInterface
  outside := identityExterior
  proper_inside := identityRegion_isProper
  interface_nonempty := identityInterface_nonempty
  outside_nonempty := identityExterior_nonempty
  labels := {
    inside_interface_disjoint := identityRegion_interface_disjoint
    interface_outside_disjoint := identityInterface_exterior_disjoint
    inside_outside_disjoint := identityRegion_exterior_disjoint
    exhaustive := identity_three_way
  }
  interface_is_frontier := identityRegion_frontier

def radialInterfaceApproximation
    (anchors : forall n : Nat, ContourState (n + 1)) :
    InterfaceApproximation identityInterface where
  carrier n := closedContourCarrier (n + 1)
  envelope n := Metric.hausdorffDist
    (closedContourCarrier (n + 1)) identityInterface
  target_nonempty := identityInterface_nonempty
  target_compact := radial_identity_separation.interface_compact
  carrier_nonempty n :=
    closedContourCarrier_nonempty (Nat.succ_pos n) (anchors n)
  carrier_compact n :=
    closedContourCarrier_compact (Nat.succ_pos n) (anchors n)
  hausdorff_le _ := le_rfl
  envelope_tendsto_zero := by
    have hSequence :
        (fun n => Metric.hausdorffDist
          (closedContourCarrier (n + 1)) identityInterface) =
          identityFrontierHausdorffSequence := by
      funext n
      unfold identityFrontierHausdorffSequence
      rw [identityRegion_frontier]
    rw [hSequence]
    exact identityFrontierHausdorffSequence_tendsto_zero anchors

def radialComputableBoundaryModel
    (anchors : forall n : Nat, ContourState (n + 1)) :
    ComputableBoundaryModel AmbientPlane where
  toBoundaryModel := radialBoundaryModel
  approximation := radialInterfaceApproximation anchors

theorem radial_abstract_convergence
    (anchors : forall n : Nat, ContourState (n + 1)) :
    Tendsto
      (fun n => Metric.hausdorffDist
        (closedContourCarrier (n + 1)) (frontier identityRegion))
      atTop (nhds 0) := by
  exact (radialComputableBoundaryModel anchors).converges_to_actual_frontier

end
end AbstractBoundaryApproximation
end BoundaryOfSelf
