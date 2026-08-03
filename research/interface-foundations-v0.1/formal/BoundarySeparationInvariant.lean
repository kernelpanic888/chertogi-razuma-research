import BoundaryOfSelf
import CompactHausdorffAttainment
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace BoundaryOfSelf
namespace BoundarySeparationInvariant

noncomputable section

open Filter
open LocalSegmentRealCompletion
open OneSidedEuclideanContourBound
open ConcreteRadialContourTraversal
open HausdorffStyleConvergence
open StandardHausdorffMetricBridge
open CompactHausdorffAttainment

/-!
IF-BS-22F-C returns the completed contour theorem to IF-BS-01. Identity is
represented by a nonempty proper open region; its interface is the actual
topological frontier, and the finite contour family converges to that frontier.
-/

def identityRegion : Set AmbientPlane :=
  Metric.ball 0 targetRadius

def identityInterface : Set AmbientPlane :=
  Metric.sphere 0 targetRadius

def identityExterior : Set AmbientPlane :=
  (Metric.closedBall 0 targetRadius)ᶜ

def planeProjection (point : AmbientPlane) : RealPlanePoint :=
  { x := point 0, y := point 1 }

theorem planeEmbedding_planeProjection (point : AmbientPlane) :
    planeEmbedding (planeProjection point) = point := by
  ext i
  fin_cases i <;> rfl

theorem squaredRadius_planeProjection (point : AmbientPlane) :
    squaredRadius (planeProjection point) = ‖point‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [planeProjection, squaredRadius, Fin.sum_univ_two]

theorem targetCircleCarrier_eq_identityInterface :
    targetCircleCarrier = identityInterface := by
  ext point
  constructor
  · rintro ⟨target, hTarget, rfl⟩
    unfold identityInterface
    rw [Metric.mem_sphere, target_embedding_dist_zero hTarget]
  · intro hInterface
    refine ⟨planeProjection point, ?_,
      (planeEmbedding_planeProjection point).symm⟩
    unfold onTargetCircle
    rw [squaredRadius_planeProjection]
    have hNorm : ‖point‖ = targetRadius := by
      simpa [identityInterface, dist_zero_right] using hInterface
    rw [hNorm, targetRadius_sq]

theorem closedTargetCarrier_eq_identityInterface :
    closedTargetCarrier = identityInterface := by
  unfold closedTargetCarrier
  rw [targetCircleCarrier_eq_identityInterface]
  exact Metric.closure_sphere

theorem identityRegion_frontier :
    frontier identityRegion = identityInterface := by
  unfold identityRegion identityInterface
  exact frontier_ball 0 targetRadius_pos.ne'

theorem identityRegion_nonempty : identityRegion.Nonempty := by
  refine ⟨0, ?_⟩
  simpa [identityRegion, Metric.mem_ball] using targetRadius_pos

def exteriorSeedPoint : RealPlanePoint :=
  { x := 2, y := 0 }

def exteriorSeed : AmbientPlane :=
  planeEmbedding exteriorSeedPoint

theorem exteriorSeed_dist_zero : dist exteriorSeed 0 = 2 := by
  rw [dist_zero_right]
  unfold exteriorSeed
  rw [norm_planeEmbedding_eq_radialNorm]
  norm_num [exteriorSeedPoint, radialNorm, squaredRadius]

theorem targetRadius_lt_two : targetRadius < 2 := by
  have hSq := targetRadius_sq
  have hNonnegative := targetRadius_nonneg
  nlinarith

theorem identityExterior_nonempty : identityExterior.Nonempty := by
  refine ⟨exteriorSeed, ?_⟩
  unfold identityExterior
  rw [Set.mem_compl_iff, Metric.mem_closedBall, exteriorSeed_dist_zero]
  exact not_le.mpr targetRadius_lt_two

theorem identityInterface_nonempty : identityInterface.Nonempty := by
  rw [← targetCircleCarrier_eq_identityInterface]
  exact targetCircleCarrier_nonempty

theorem identityRegion_isProper :
    ProperRegion (fun point => point ∈ identityRegion) := by
  refine ⟨identityRegion_nonempty, ?_⟩
  rcases identityExterior_nonempty with ⟨point, hPoint⟩
  refine ⟨point, ?_⟩
  intro hInside
  have hInsideClosed : point ∈ Metric.closedBall 0 targetRadius :=
    Metric.ball_subset_closedBall hInside
  exact hPoint hInsideClosed

theorem identityRegion_interface_disjoint :
    Disjoint identityRegion identityInterface := by
  rw [Set.disjoint_left]
  intro point hInside hInterface
  have hLt := Metric.mem_ball.1 hInside
  have hEq := Metric.mem_sphere.1 hInterface
  linarith

theorem identityInterface_exterior_disjoint :
    Disjoint identityInterface identityExterior := by
  rw [Set.disjoint_left]
  intro point hInterface hExterior
  apply hExterior
  exact Metric.sphere_subset_closedBall hInterface

theorem identityRegion_exterior_disjoint :
    Disjoint identityRegion identityExterior := by
  rw [Set.disjoint_left]
  intro point hInside hExterior
  apply hExterior
  exact Metric.ball_subset_closedBall hInside

theorem identity_three_way (point : AmbientPlane) :
    point ∈ identityRegion ∨ point ∈ identityInterface ∨
      point ∈ identityExterior := by
  rcases lt_trichotomy (dist point 0) targetRadius with hInside | hInterface | hOutside
  · exact Or.inl hInside
  · exact Or.inr (Or.inl hInterface)
  · exact Or.inr (Or.inr (not_le.mpr hOutside))

structure SeparationInvariant
    (inside interface outside : Set AmbientPlane) : Prop where
  inside_nonempty : inside.Nonempty
  interface_nonempty : interface.Nonempty
  outside_nonempty : outside.Nonempty
  inside_interface_disjoint : Disjoint inside interface
  interface_outside_disjoint : Disjoint interface outside
  inside_outside_disjoint : Disjoint inside outside
  exhaustive : forall point, point ∈ inside ∨ point ∈ interface ∨ point ∈ outside
  interface_compact : IsCompact interface
  interface_is_frontier : frontier inside = interface

theorem radial_identity_separation :
    SeparationInvariant identityRegion identityInterface identityExterior where
  inside_nonempty := identityRegion_nonempty
  interface_nonempty := identityInterface_nonempty
  outside_nonempty := identityExterior_nonempty
  inside_interface_disjoint := identityRegion_interface_disjoint
  interface_outside_disjoint := identityInterface_exterior_disjoint
  inside_outside_disjoint := identityRegion_exterior_disjoint
  exhaustive := identity_three_way
  interface_compact := by
    rw [← closedTargetCarrier_eq_identityInterface]
    exact closedTargetCarrier_compact
  interface_is_frontier := identityRegion_frontier

theorem contour_approximates_identity_frontier {m : Nat} (hm : 0 < m)
    (anchor : ContourState m) :
    Metric.hausdorffDist (closedContourCarrier m) (frontier identityRegion) <=
      hausdorffEnvelope m := by
  rw [identityRegion_frontier, ← closedTargetCarrier_eq_identityInterface]
  exact closed_carriers_hausdorffDist_le hm anchor

def identityFrontierHausdorffSequence (n : Nat) : Real :=
  Metric.hausdorffDist (closedContourCarrier (n + 1))
    (frontier identityRegion)

theorem identityFrontierHausdorffSequence_eq_standard :
    identityFrontierHausdorffSequence = standardHausdorffSequence := by
  funext n
  unfold identityFrontierHausdorffSequence standardHausdorffSequence
  rw [identityRegion_frontier, ← closedTargetCarrier_eq_identityInterface]

theorem identityFrontierHausdorffSequence_tendsto_zero
    (_anchors : forall n : Nat, ContourState (n + 1)) :
    Tendsto identityFrontierHausdorffSequence atTop (nhds 0) := by
  rw [identityFrontierHausdorffSequence_eq_standard]
  exact standardHausdorffSequence_tendsto_zero _anchors

end
end BoundarySeparationInvariant
end BoundaryOfSelf

#print axioms BoundaryOfSelf.BoundarySeparationInvariant.targetCircleCarrier_eq_identityInterface
#print axioms BoundaryOfSelf.BoundarySeparationInvariant.identityRegion_frontier
#print axioms BoundaryOfSelf.BoundarySeparationInvariant.identityRegion_isProper
#print axioms BoundaryOfSelf.BoundarySeparationInvariant.radial_identity_separation
#print axioms BoundaryOfSelf.BoundarySeparationInvariant.contour_approximates_identity_frontier
#print axioms BoundaryOfSelf.BoundarySeparationInvariant.identityFrontierHausdorffSequence_tendsto_zero
