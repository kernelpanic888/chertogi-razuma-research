import IsometricBoundaryTransport

namespace BoundaryOfSelf
namespace BiLipschitzBoundaryTransport

noncomputable section

open Filter
open AbstractBoundaryApproximation

universe u v

variable {X : Type u} {Y : Type v}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A homeomorphic coordinate change with explicit metric control in both
directions. The forward constant controls transported approximation error. -/
structure ControlledEquiv (X : Type u) (Y : Type v)
    [PseudoMetricSpace X] [PseudoMetricSpace Y] where
  toHomeomorph : X ≃ₜ Y
  forwardConstant : NNReal
  inverseConstant : NNReal
  forward_lipschitz : LipschitzWith forwardConstant toHomeomorph
  inverse_lipschitz : LipschitzWith inverseConstant toHomeomorph.symm

namespace ControlledEquiv

instance : CoeFun (ControlledEquiv X Y) (fun _ => X → Y) :=
  ⟨fun controlled => controlled.toHomeomorph⟩

theorem injective (controlled : ControlledEquiv X Y) :
    Function.Injective controlled :=
  controlled.toHomeomorph.injective

theorem surjective (controlled : ControlledEquiv X Y) :
    Function.Surjective controlled :=
  controlled.toHomeomorph.surjective

theorem continuous (controlled : ControlledEquiv X Y) :
    Continuous controlled :=
  controlled.toHomeomorph.continuous

end ControlledEquiv

def transportSet (controlled : ControlledEquiv X Y) (region : Set X) : Set Y :=
  controlled '' region

theorem transportSet_nonempty (controlled : ControlledEquiv X Y)
    {region : Set X} (hRegion : region.Nonempty) :
    (transportSet controlled region).Nonempty := by
  exact hRegion.image controlled

theorem transportSet_disjoint (controlled : ControlledEquiv X Y)
    {first second : Set X} (hDisjoint : Disjoint first second) :
    Disjoint (transportSet controlled first) (transportSet controlled second) := by
  rw [Set.disjoint_left]
  intro point hFirst hSecond
  rcases hFirst with ⟨firstPoint, hFirstPoint, rfl⟩
  rcases hSecond with ⟨secondPoint, hSecondPoint, hSameImage⟩
  have hSamePoint : secondPoint = firstPoint :=
    controlled.injective hSameImage
  exact Set.disjoint_left.1 hDisjoint hFirstPoint
    (hSamePoint ▸ hSecondPoint)

theorem transportSet_frontier (controlled : ControlledEquiv X Y)
    (region : Set X) :
    frontier (transportSet controlled region) =
      transportSet controlled (frontier region) := by
  exact (controlled.toHomeomorph.image_frontier region).symm

theorem compact_hausdorffDist_le_iff_witnesses
    {firstSet secondSet : Set X} {radius : Real}
    (hFirstCompact : IsCompact firstSet)
    (hSecondCompact : IsCompact secondSet)
    (hFirstNonempty : firstSet.Nonempty)
    (hSecondNonempty : secondSet.Nonempty)
    (hRadius : 0 <= radius) :
    Metric.hausdorffDist firstSet secondSet <= radius ↔
      (∀ first ∈ firstSet, ∃ second ∈ secondSet,
        dist first second <= radius) /\
      (∀ second ∈ secondSet, ∃ first ∈ firstSet,
        dist second first <= radius) := by
  constructor
  · intro hHausdorff
    have hFiniteForward :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        hFirstNonempty hSecondNonempty
        hFirstCompact.isBounded hSecondCompact.isBounded
    have hFiniteReverse :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        hSecondNonempty hFirstNonempty
        hSecondCompact.isBounded hFirstCompact.isBounded
    constructor
    · intro first hFirst
      rcases hSecondCompact.exists_infDist_eq_dist
          hSecondNonempty first with
        ⟨second, hSecond, hNearest⟩
      refine ⟨second, hSecond, ?_⟩
      calc
        dist first second = Metric.infDist first secondSet := hNearest.symm
        _ <= Metric.hausdorffDist firstSet secondSet :=
          Metric.infDist_le_hausdorffDist_of_mem hFirst hFiniteForward
        _ <= radius := hHausdorff
    · intro second hSecond
      rcases hFirstCompact.exists_infDist_eq_dist
          hFirstNonempty second with
        ⟨first, hFirst, hNearest⟩
      refine ⟨first, hFirst, ?_⟩
      calc
        dist second first = Metric.infDist second firstSet := hNearest.symm
        _ <= Metric.hausdorffDist secondSet firstSet :=
          Metric.infDist_le_hausdorffDist_of_mem hSecond hFiniteReverse
        _ = Metric.hausdorffDist firstSet secondSet :=
          Metric.hausdorffDist_comm
        _ <= radius := hHausdorff
  · rintro ⟨hForward, hReverse⟩
    exact Metric.hausdorffDist_le_of_mem_dist hRadius hForward hReverse

theorem hausdorffDist_transport_le (controlled : ControlledEquiv X Y)
    {firstSet secondSet : Set X}
    (hFirstCompact : IsCompact firstSet)
    (hSecondCompact : IsCompact secondSet)
    (hFirstNonempty : firstSet.Nonempty)
    (hSecondNonempty : secondSet.Nonempty) :
    Metric.hausdorffDist
      (transportSet controlled firstSet)
      (transportSet controlled secondSet) <=
      controlled.forwardConstant *
        Metric.hausdorffDist firstSet secondSet := by
  have hWitnesses :=
    (compact_hausdorffDist_le_iff_witnesses
      hFirstCompact hSecondCompact hFirstNonempty hSecondNonempty
      Metric.hausdorffDist_nonneg).1 le_rfl
  refine Metric.hausdorffDist_le_of_mem_dist
    (mul_nonneg controlled.forwardConstant.coe_nonneg
      Metric.hausdorffDist_nonneg) ?_ ?_
  · intro imagePoint hImagePoint
    rcases hImagePoint with ⟨sourcePoint, hSourcePoint, rfl⟩
    rcases hWitnesses.1 sourcePoint hSourcePoint with
      ⟨targetPoint, hTargetPoint, hDistance⟩
    refine ⟨controlled targetPoint, ⟨targetPoint, hTargetPoint, rfl⟩, ?_⟩
    exact controlled.forward_lipschitz.dist_le_mul_of_le hDistance
  · intro imagePoint hImagePoint
    rcases hImagePoint with ⟨targetPoint, hTargetPoint, rfl⟩
    rcases hWitnesses.2 targetPoint hTargetPoint with
      ⟨sourcePoint, hSourcePoint, hDistance⟩
    refine ⟨controlled sourcePoint, ⟨sourcePoint, hSourcePoint, rfl⟩, ?_⟩
    exact controlled.forward_lipschitz.dist_le_mul_of_le hDistance

def transportBoundaryModel (controlled : ControlledEquiv X Y)
    (model : BoundaryModel X) : BoundaryModel Y where
  inside := transportSet controlled model.inside
  interface := transportSet controlled model.interface
  outside := transportSet controlled model.outside
  proper_inside := by
    rcases model.proper_inside with ⟨⟨insidePoint, hInside⟩,
      ⟨outsidePoint, hOutside⟩⟩
    refine ⟨⟨controlled insidePoint, insidePoint, hInside, rfl⟩,
      ⟨controlled outsidePoint, ?_⟩⟩
    intro hTransportedInside
    rcases hTransportedInside with
      ⟨sourcePoint, hSourceInside, hSameImage⟩
    have hSamePoint : sourcePoint = outsidePoint :=
      controlled.injective hSameImage
    exact hOutside (hSamePoint ▸ hSourceInside)
  interface_nonempty := transportSet_nonempty controlled model.interface_nonempty
  outside_nonempty := transportSet_nonempty controlled model.outside_nonempty
  labels := {
    inside_interface_disjoint :=
      transportSet_disjoint controlled model.labels.inside_interface_disjoint
    interface_outside_disjoint :=
      transportSet_disjoint controlled model.labels.interface_outside_disjoint
    inside_outside_disjoint :=
      transportSet_disjoint controlled model.labels.inside_outside_disjoint
    exhaustive := by
      intro point
      rcases controlled.surjective point with ⟨sourcePoint, rfl⟩
      rcases model.labels.exhaustive sourcePoint with
        hInside | hInterface | hOutside
      · exact Or.inl ⟨sourcePoint, hInside, rfl⟩
      · exact Or.inr (Or.inl ⟨sourcePoint, hInterface, rfl⟩)
      · exact Or.inr (Or.inr ⟨sourcePoint, hOutside, rfl⟩)
  }
  interface_is_frontier := by
    calc
      frontier (transportSet controlled model.inside) =
          transportSet controlled (frontier model.inside) :=
        transportSet_frontier controlled model.inside
      _ = transportSet controlled model.interface := by
        rw [model.interface_is_frontier]

def transportInterfaceApproximation (controlled : ControlledEquiv X Y)
    {target : Set X} (approximation : InterfaceApproximation target) :
    InterfaceApproximation (transportSet controlled target) where
  carrier n := transportSet controlled (approximation.carrier n)
  envelope n := controlled.forwardConstant * approximation.envelope n
  target_nonempty := transportSet_nonempty controlled approximation.target_nonempty
  target_compact := approximation.target_compact.image controlled.continuous
  carrier_nonempty n :=
    transportSet_nonempty controlled (approximation.carrier_nonempty n)
  carrier_compact n :=
    (approximation.carrier_compact n).image controlled.continuous
  hausdorff_le n := by
    calc
      Metric.hausdorffDist
          (transportSet controlled (approximation.carrier n))
          (transportSet controlled target) <=
          controlled.forwardConstant *
            Metric.hausdorffDist (approximation.carrier n) target :=
        hausdorffDist_transport_le controlled
          (approximation.carrier_compact n) approximation.target_compact
          (approximation.carrier_nonempty n) approximation.target_nonempty
      _ <= controlled.forwardConstant * approximation.envelope n :=
        mul_le_mul_of_nonneg_left (approximation.hausdorff_le n)
          controlled.forwardConstant.coe_nonneg
  envelope_tendsto_zero := by
    simpa using tendsto_const_nhds.mul approximation.envelope_tendsto_zero

def transportComputableBoundaryModel (controlled : ControlledEquiv X Y)
    (model : ComputableBoundaryModel X) : ComputableBoundaryModel Y where
  toBoundaryModel := transportBoundaryModel controlled model.toBoundaryModel
  approximation :=
    transportInterfaceApproximation controlled model.approximation

theorem transported_model_error_le (controlled : ControlledEquiv X Y)
    (model : ComputableBoundaryModel X) (n : Nat) :
    Metric.hausdorffDist
      ((transportComputableBoundaryModel controlled model).approximation.carrier n)
      (transportComputableBoundaryModel controlled model).interface <=
    controlled.forwardConstant * model.approximation.envelope n := by
  exact (transportComputableBoundaryModel controlled model).approximation.hausdorff_le n

theorem transported_model_converges_to_actual_frontier
    (controlled : ControlledEquiv X Y) (model : ComputableBoundaryModel X) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((transportComputableBoundaryModel controlled model).approximation.carrier n)
        (frontier (transportComputableBoundaryModel controlled model).inside))
      atTop (nhds 0) := by
  exact (transportComputableBoundaryModel controlled model).converges_to_actual_frontier

end
end BiLipschitzBoundaryTransport
end BoundaryOfSelf
