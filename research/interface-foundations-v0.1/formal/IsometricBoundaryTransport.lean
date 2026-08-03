import AbstractBoundaryApproximation

namespace BoundaryOfSelf
namespace IsometricBoundaryTransport

noncomputable section

open Filter
open AbstractBoundaryApproximation

universe u v

variable {X : Type u} {Y : Type v}
variable [PseudoMetricSpace X] [PseudoMetricSpace Y]

def transportSet (equivalence : X ≃ᵢ Y) (region : Set X) : Set Y :=
  equivalence '' region

theorem transportSet_nonempty (equivalence : X ≃ᵢ Y)
    {region : Set X} (hRegion : region.Nonempty) :
    (transportSet equivalence region).Nonempty := by
  exact hRegion.image equivalence

theorem transportSet_disjoint (equivalence : X ≃ᵢ Y)
    {first second : Set X} (hDisjoint : Disjoint first second) :
    Disjoint (transportSet equivalence first) (transportSet equivalence second) := by
  rw [Set.disjoint_left]
  intro point hFirst hSecond
  rcases hFirst with ⟨firstPoint, hFirstPoint, rfl⟩
  rcases hSecond with ⟨secondPoint, hSecondPoint, hSameImage⟩
  have hSamePoint : secondPoint = firstPoint :=
    equivalence.injective hSameImage
  exact Set.disjoint_left.1 hDisjoint hFirstPoint
    (hSamePoint ▸ hSecondPoint)

theorem transportSet_frontier (equivalence : X ≃ᵢ Y) (region : Set X) :
    frontier (transportSet equivalence region) =
      transportSet equivalence (frontier region) := by
  exact (equivalence.toHomeomorph.image_frontier region).symm

theorem transportSet_hausdorffDist (equivalence : X ≃ᵢ Y)
    (first second : Set X) :
    Metric.hausdorffDist
      (transportSet equivalence first) (transportSet equivalence second) =
      Metric.hausdorffDist first second := by
  exact Metric.hausdorffDist_image equivalence.isometry

def transportBoundaryModel (equivalence : X ≃ᵢ Y)
    (model : BoundaryModel X) : BoundaryModel Y where
  inside := transportSet equivalence model.inside
  interface := transportSet equivalence model.interface
  outside := transportSet equivalence model.outside
  proper_inside := by
    rcases model.proper_inside with ⟨⟨insidePoint, hInside⟩,
      ⟨outsidePoint, hOutside⟩⟩
    refine ⟨⟨equivalence insidePoint, insidePoint, hInside, rfl⟩,
      ⟨equivalence outsidePoint, ?_⟩⟩
    intro hTransportedInside
    rcases hTransportedInside with
      ⟨sourcePoint, hSourceInside, hSameImage⟩
    have hSamePoint : sourcePoint = outsidePoint :=
      equivalence.injective hSameImage
    exact hOutside (hSamePoint ▸ hSourceInside)
  interface_nonempty := transportSet_nonempty equivalence model.interface_nonempty
  outside_nonempty := transportSet_nonempty equivalence model.outside_nonempty
  labels := {
    inside_interface_disjoint :=
      transportSet_disjoint equivalence model.labels.inside_interface_disjoint
    interface_outside_disjoint :=
      transportSet_disjoint equivalence model.labels.interface_outside_disjoint
    inside_outside_disjoint :=
      transportSet_disjoint equivalence model.labels.inside_outside_disjoint
    exhaustive := by
      intro point
      rcases equivalence.surjective point with ⟨sourcePoint, rfl⟩
      rcases model.labels.exhaustive sourcePoint with
        hInside | hInterface | hOutside
      · exact Or.inl ⟨sourcePoint, hInside, rfl⟩
      · exact Or.inr (Or.inl ⟨sourcePoint, hInterface, rfl⟩)
      · exact Or.inr (Or.inr ⟨sourcePoint, hOutside, rfl⟩)
  }
  interface_is_frontier := by
    calc
      frontier (transportSet equivalence model.inside) =
          transportSet equivalence (frontier model.inside) :=
        transportSet_frontier equivalence model.inside
      _ = transportSet equivalence model.interface := by
        rw [model.interface_is_frontier]

def transportInterfaceApproximation (equivalence : X ≃ᵢ Y)
    {target : Set X} (approximation : InterfaceApproximation target) :
    InterfaceApproximation (transportSet equivalence target) where
  carrier n := transportSet equivalence (approximation.carrier n)
  envelope := approximation.envelope
  target_nonempty := transportSet_nonempty equivalence approximation.target_nonempty
  target_compact := approximation.target_compact.image equivalence.continuous
  carrier_nonempty n :=
    transportSet_nonempty equivalence (approximation.carrier_nonempty n)
  carrier_compact n :=
    (approximation.carrier_compact n).image equivalence.continuous
  hausdorff_le n := by
    rw [transportSet_hausdorffDist]
    exact approximation.hausdorff_le n
  envelope_tendsto_zero := approximation.envelope_tendsto_zero

def transportComputableBoundaryModel (equivalence : X ≃ᵢ Y)
    (model : ComputableBoundaryModel X) : ComputableBoundaryModel Y where
  toBoundaryModel := transportBoundaryModel equivalence model.toBoundaryModel
  approximation :=
    transportInterfaceApproximation equivalence model.approximation

theorem transported_model_exact_error (equivalence : X ≃ᵢ Y)
    (model : ComputableBoundaryModel X) (n : Nat) :
    Metric.hausdorffDist
      ((transportComputableBoundaryModel equivalence model).approximation.carrier n)
      (transportComputableBoundaryModel equivalence model).interface =
    Metric.hausdorffDist
      (model.approximation.carrier n) model.interface := by
  exact transportSet_hausdorffDist equivalence
    (model.approximation.carrier n) model.interface

theorem transported_model_converges_to_actual_frontier
    (equivalence : X ≃ᵢ Y) (model : ComputableBoundaryModel X) :
    Tendsto
      (fun n => Metric.hausdorffDist
        ((transportComputableBoundaryModel equivalence model).approximation.carrier n)
        (frontier (transportComputableBoundaryModel equivalence model).inside))
      atTop (nhds 0) := by
  exact (transportComputableBoundaryModel equivalence model).converges_to_actual_frontier

end
end IsometricBoundaryTransport
end BoundaryOfSelf
